
{-# LANGUAGE GADTs
           , EmptyDataDecls
           , StandaloneDeriving
           , MultiParamTypeClasses
           , TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , UndecidableInstances
           , NoMonomorphismRestriction
           , OverloadedStrings
           #-}
import Unbound.LocallyNameless
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Trans.Maybe
import Control.Applicative
import Control.Monad
import Control.Monad.Error
import qualified Text.PrettyPrint as PP
import Text.PrettyPrint (Doc, (<+>), (<>))
import Data.String
import Debug.Trace

-- DATA TYPES

data Polarity = Unspecified | Positive | Negative | Fixed
    deriving (Show, Eq)

data Constant = Star
              | StarStar
              | Box
              | BoxBox
    deriving (Show, Ord, Eq)

data Expr = Constant Constant
          | Var (Name Expr)
          | App Expr Expr
          | Lambda Expr (Bind (Name Expr) Expr)
          | Pi Polarity Expr (Bind (Name Expr) Expr)
    deriving (Show)

-- FRONTEND LANGUAGE

data UExpr = UVar (Name UExpr)
           | UApp UExpr UExpr
           | ULambda (Bind (Name UExpr) UExpr)
    deriving (Show)

-- UNBOUND NONSENSE

$(derive [''Expr, ''Constant, ''Polarity])
$(derive [''UExpr])
instance Alpha Expr
instance Alpha Constant
instance Alpha UExpr
instance Alpha Polarity
instance Subst Expr Constant where
instance Subst Expr Polarity where
instance Subst Expr Expr where
    isvar (Var v) = Just (SubstName v)
    isvar _ = Nothing
instance Subst UExpr UExpr where
    isvar (UVar v) = Just (SubstName v)
    isvar _ = Nothing

-- POLARITY IS A LATTICE

lub Unspecified _ = Unspecified
lub _ Unspecified = Unspecified
lub Positive Negative = Unspecified
lub Positive _ = Positive
lub Negative Positive = Unspecified
lub Negative _ = Negative
lub Fixed p = p

instance Num Polarity where
    negate Positive = Negative
    negate Negative = Positive
    negate p = p

    Fixed * _ = Fixed
    _ * Fixed = Fixed
    Unspecified * _ = Unspecified
    _ * Unspecified = Unspecified
    Positive * Positive = Positive
    Positive * Negative = Negative
    Negative * Negative = Positive
    Negative * Positive = Negative

    fromInteger = error "fromInteger not defined on polarity"
    (+) = error "addition not defined on polarity"
    abs = error "abs not defined on polarity"
    signum = error "signum not defined on polarity"

-- MONAD PLUMBING

done :: MonadPlus m => m a
done = mzero

type M = ErrorT String LFreshM

runM = either error id . runLFreshM . runErrorT

-- EVALUATION AND TYPE CHECKING

-- XXX I hope this is right
beta :: Expr -> MaybeT M Expr
beta (Var _) = done
beta (Constant _) = done
beta (Pi p t z) = lunbind z $ \(x, e) ->
        Pi p <$> beta t <*> pure (bind x e)
    <|> Pi p <$> pure t <*> fmap (bind x) (beta e)
beta (Lambda t z) = lunbind z $ \(x, e) -> do
        Lambda <$> beta t <*> pure (bind x e)
    <|> Lambda <$> pure t <*> fmap (bind x) (beta e)
beta (App (Lambda _ z) e) = lunbind z $ \(x, e') -> do
        return $ subst x e e'
beta (App t1 t2) =
        App <$> beta t1 <*> pure t2
    <|> App <$> pure t1 <*> beta t2

normalize :: Expr -> M Expr
normalize t = do
    m <- runMaybeT (beta t)
    case m of
        Just t' -> normalize t'
        Nothing -> return t

axiom :: Constant -> M Constant
axiom Star = return Box
axiom StarStar = return BoxBox
axiom Box = throwError "axiom: ☐ is not typeable"
axiom BoxBox = throwError "axiom: ☐☐ is not typeable"

normalizingSubst n e e' = normalize (subst n e e')

rel a b c = ((a, b), c)
relations = Map.fromList
    [ rel Star  Star        Star
    , rel Star  StarStar    StarStar
    , rel Box   Star        StarStar
    , rel Box   StarStar    StarStar
    , rel Box   Box         Box
    , rel Box   BoxBox      BoxBox
    ]

polarityOf :: Map (Name Expr) Expr -> Name Expr -> Expr -> M Polarity
polarityOf _ _ (Constant _) = return Fixed
polarityOf _ n (Var x) | n == x    = return Positive
                       | otherwise = return Fixed
polarityOf m n (App t1 t2) = do
    k <- typeOf m t1
    p1 <- polarityOf m n t1
    p2 <- polarityOf m n t2
    case k of
        Pi p _ _ -> return (lub p1 (p * p2))
        _ -> throwError ("polarityOf: attempting to apply non-pi type")
polarityOf m n (Lambda t z) = lunbind z $ \(x, e) -> do
    if Set.member n (fv t)
        then return Unspecified -- conservative choice
        else polarityOf (Map.insert x t m) n e
polarityOf m n (Pi _ t1 z) = lunbind z $ \(x, t2) -> do
    p1 <- polarityOf m n t1
    p2 <- polarityOf (Map.insert x t1 m) n t2
    return (lub (-p1) p2)

typeOf :: Map (Name Expr) Expr -> Expr -> M Expr
typeOf _ (Constant c) = Constant <$> axiom c
typeOf m (Var n) = maybe (throwError ("typeOf: unbound variable " ++ show n)) return (Map.lookup n m)
typeOf m e@(App f a) = do
    tf <- typeOf m f
    ta <- typeOf m a
    case tf of
        Pi _ ta' z | ta `aeq` ta' -> lunbind z $ \(x, tb) -> normalizingSubst x a tb
                   | otherwise -> throwError ("typeOf: ill-typed application '" ++ ppshow e ++ "', expected '" ++ ppshow ta' ++ "' but got '" ++ ppshow ta ++ "'")
        _ -> throwError ("typeOf: attempting to apply non-pi type '" ++ ppshow tf ++ "' in '" ++ ppshow e ++ "'")
typeOf m (Lambda ta z) = lunbind z $ \(x, b) -> do
    t1 <- typeOf m ta
    let m' = Map.insert x ta m
    tb <- typeOf m' b
    t2 <- typeOf m' tb
    case (t1, t2) of
        (Constant s1, Constant s2) -> case Map.lookup (s1, s2) relations of
            Nothing -> throwError "typeOf: lambda relation violation"
            Just _ -> do
                p <- polarityOf m' x b
                return (Pi p ta (bind x tb))
        _ -> throwError "typeOf: lambda not sorts"
typeOf m (Pi _ ta z) = lunbind z $ \(x, tb) -> do
    -- XXX polarity does not seem to affect the type of pi
    t1 <- typeOf m ta
    t2 <- typeOf (Map.insert x ta m) tb
    case (t1, t2) of
        (Constant s1, Constant s2) -> case Map.lookup (s1, s2) relations of
            Nothing -> throwError "typeOf: pi relation violation"
            Just s3 -> return (Constant s3)
        _ -> throwError "typeOf: pi not sorts"

tof = runM . typeOf library

-- TYPE INFERENCE

erz = runM . erase library

erase :: Map (Name Expr) Expr -> Expr -> M UExpr
erase m e@(Var n) = do
    case Map.lookup n m of
        Nothing -> throwError "erase: unbound variable"
        Just t -> do
            k <- typeOf m t
            let r = return (UVar (translate n))
            case k of
                Constant Star -> r
                Constant StarStar -> r
                _ -> throwError ("erase: non-computational variable " ++ ppshow e ++ " was not erased")
erase m (Lambda t z) = lunbind z $ \(n, e) -> do
    -- need to decide if it has computational content
    k <- typeOf m t
    case k of
        Constant Star -> ULambda . bind (translate n) <$> erase (Map.insert n t m) e
        Constant StarStar -> throwError "erase: lambda takes polytype as argument"
        _ -> erase (Map.insert n t m) e
erase m e@(App e1 e2) = do
    t <- typeOf m e2
    k <- typeOf m t
    let r = UApp <$> erase m e1 <*> erase m e2
    case k of
        Constant Star -> r
        Constant StarStar -> r
        _ -> erase m e1
erase _ (Pi _ _ _) = throwError "erase: pi has no computational content"
erase _ (Constant _) = throwError "erase: constant has no computational content"

-- PRETTY PRINTING

class Pretty p where
    ppr :: (Applicative m, LFresh m) => Int -> p -> m Doc

pprint = putStrLn . ppshow
ppshow = PP.render . runLFreshM . ppr 0

instance Pretty Constant where
    ppr _ Box = return (PP.text "☐")
    ppr _ BoxBox = return (PP.text "☐☐")
    ppr _ Star = return (PP.text "★")
    ppr _ StarStar = return (PP.text "★★")

instance Pretty Polarity where
    ppr _ = pprPolarity
    -- ppr _ = pprNop

pprNop _ = return $ PP.text ""
pprPolarity Positive = return $ PP.text "⁺"
pprPolarity Negative = return $ PP.text "⁻"
pprPolarity Fixed = return $ PP.text "°"
pprPolarity Unspecified = return $ PP.text "±"

nopEq x y = if x == y then return (PP.text "") else ppr 0 y

instance Pretty Expr where
    ppr _ (Var n) = return (PP.text (show n))
    ppr _ (Constant c) = ppr 0 c
    ppr p (Lambda t z) = pbinds p "λ" t z
    -- not perfect: want to look at the sorts to get a better idea for
    -- how to print it...
    ppr p (Pi pm t z) = fmap (prettyParen (p > 0)) . lunbind z $ \(x, e) -> do
        if Set.member x (fv e)
            then pbind "Π" x <$> nopEq Unspecified pm <*> ppr 0 t <*> ppr 0 e
            else parr' <$> ppr 0 t <*> nopEq Positive pm <*> ppr 0 e
    ppr p (App e1 e2) = prettyParen (p > 1) <$> ((<+>) <$> ppr 1 e1 <*> ppr 2 e2)

instance Pretty UExpr where
    ppr _ (UVar n) = return (PP.text (show n))
    ppr p (ULambda z) = fmap (prettyParen (p > 0)) . lunbind z $ \(x,e) -> lam x <$> ppr 0 e
        where lam x e = PP.hang (PP.text "λ" <> PP.text (show x) <> PP.text ".") 2 e
    ppr p (UApp e1 e2) = prettyParen (p > 1) <$> ((<+>) <$> ppr 1 e1 <*> ppr 2 e2)

prettyParen True = PP.parens
prettyParen False = id
parr' a b c = PP.hang a (-2) (PP.text "→" <> b <+> c)
pbind b n pm k e = PP.hang (PP.text b <> pm <> PP.parens (PP.text (show n) <+> PP.colon <+> k) <> PP.text ".") 2 e
pbinds p c k b = fmap (prettyParen (p > 0)) . lunbind b $ \(n,t) ->
    pbind c n (PP.text "") <$> ppr 0 k <*> ppr 0 t

-- EXAMPLE SUPPORT CODE

infixl 9 #
infixr 1 ~>

lam x t e = Lambda t $ bind (string2Name x) e
forall x t e = Pi Positive t $ bind (string2Name x) e
(#) = App
a ~> b = Pi Positive a $ bind (s2n "_") b
star = Constant Star
phi f1 f2 = forall "a" star (f1 # "a" ~> f2 # "a")

instance IsString Expr where fromString = Var . fromString
instance IsString (Name Expr) where fromString = string2Name

(!:) = (,)
infixr 1 !:

-- XXX we are taking it ON FAITH that these signatures are valid in
-- the system
library = Map.fromList . runM . mapM (\(a,b) -> normalize b >>= \b' -> return (a, b')) $
    [ "μ"       !: (star ~> star) ~> star
    , "Prod"    !: star ~> star ~> star
    , "Int"     !: star
    , "NatF"    !: star ~> star
    , "D_i"     !: star ~> star
    , "D_j"     !: star ~> star
    , "Ix_i"    !: star
    , "Ix_j"    !: star
    , "ListF"   !: star ~> star ~> star
    , "fold"    !: forall "r" star (forall "f" (star ~> star) (("f" # "r" ~> "r") ~> "μ" # "f" ~> "r"))
    , "roll"    !: forall "f" (star ~> star) ("f" # ("μ" # "f") ~> "μ" # "f")
    , "fmap"    !: forall "f" (star ~> star) (forall "a" star (forall "b" star (("a" ~> "b") ~> ("f" # "a" ~> "f" # "b"))))
    , "succF"   !: forall "n" star ("n" ~> "NatF" # "n")
    , "di2list" !: "D_i" `phi` (lam "a" star ("μ" # ("ListF" # "a")))
    , "dj2list" !: "D_j" `phi` (lam "a" star ("μ" # ("ListF" # "a")))
    , "tabulate_di" !: (lam "a" star ("Ix_i" ~> "a")) `phi` "D_i"
    , "index_di"    !: "D_i" `phi` (lam "a" star ("Ix_i" ~> "a"))
    , "index_dj"    !: "D_j" `phi` (lam "a" star ("Ix_j" ~> "a"))
    , "tabulate_dj" !: (lam "a" star ("Ix_j" ~> "a")) `phi` "D_j"
    , "bucket"  !: "D_i" # "Ix_j" ~> "D_i" `phi` (lam "a" star ("D_j" # ("μ" # ("ListF" # "a"))))
    , "pi"      !: "Ix_j" ~> "D_j" `phi` (lam "a" star "a")
    ]

-- EXAMPLES

exIdentity = lam "a" star
           . lam "x" "a"
           $ "x"

exFold = lam "r" star
       . lam "F" (star ~> star)
       . lam "f" ("F" # "r" ~> "r")
       . lam "xs" ("μ" # "F")
       $ "fold" # "r" # "F" # "f" # "xs"

exRoll = lam  "n" ("μ" # "NatF")
       $ "roll" # "NatF" # ("succF" # ("μ" # "NatF") # "n")

exBlog = lam "x" ("D_i" # "Int")
       . lam "c" ("D_i" # "Ix_j")
       . lam "divide" ("Prod" # "Int" # "Int" ~> "Int")
       . lam "plusinc" ("ListF" # "Int" # ("Prod" # "Int" # "Int") ~> "Prod" # "Int" # "Int")
       $ "tabulate_dj" # "Int" # lam "j" "Ix_j"
             ("divide" #
                ("fold" #
                    ("Prod" # "Int" # "Int") #
                    ("ListF" # "Int") #
                    "plusinc" #
                    ("pi" # "j" # ("μ" # ("ListF" # "Int")) # (("bucket" # "c" # "Int") # "x"))))
