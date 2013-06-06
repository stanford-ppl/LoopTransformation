
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
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Trans.Maybe
import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Control.Monad.Trans.Writer
import qualified Text.PrettyPrint as PP
import Text.PrettyPrint (Doc, (<+>), (<>))
import Data.String
import Debug.Trace

-- DATA TYPES

data Polarity = Unspecified | Positive | Negative | Constant
    deriving (Show, Eq)

data Sort = Star
          | StarStar
          | Box
          | BoxBox
    deriving (Show, Ord, Eq)

data Expr = Sort Sort
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

data Type = TVar (Name Type)
          | TArr Type Type
          | TSkolem (Name Expr)
          | TApp Type Type
    deriving (Show, Eq)

-- UNBOUND NONSENSE

$(derive [''Expr, ''Sort, ''Polarity])
$(derive [''UExpr])
$(derive [''Type])
instance Alpha Expr
instance Alpha Sort
instance Alpha UExpr
instance Alpha Polarity
instance Alpha Type
instance Subst Type Type where
    isvar (TVar v) = Just (SubstName v)
    isvar _ = Nothing
instance Subst Expr Sort where
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
lub Constant p = p

instance Num Polarity where
    negate Positive = Negative
    negate Negative = Positive
    negate p = p

    Constant * _ = Constant
    _ * Constant = Constant
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

type M = ErrorT String (LFreshM)

runM = either error id . runLFreshM . runErrorT

-- EVALUATION AND TYPE CHECKING

-- XXX I hope this is right
beta :: Expr -> MaybeT M Expr
beta (Var _) = done
beta (Sort _) = done
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

axiom :: Sort -> M Sort
axiom Star = return Box
axiom StarStar = return BoxBox
axiom Box = throwError "axiom: ☐ is not typeable"
axiom BoxBox = throwError "axiom: ☐☐ is not typeable"

normalizingSubst n e e' = normalize (subst n e e')

rel a b c = ((a, b), c)
relations = Map.fromList
    -- let α t : *, p : **, * : ☐, **, ☐☐
    [ rel Star  Star        Star        -- t -> t : *   (functions on monotypes are monotypes)
    , rel Star  StarStar    StarStar    -- t -> p : *   (quantifiers do not have to be prenex)
    , rel Box   Star        StarStar    -- ∀α. t : **   (quantifiers cause polytypes)
    , rel Box   StarStar    StarStar    -- ∀α. p : **   (nested quantifiers are ok)
    , rel Box   Box         Box         -- * -> * : ☐   (type functions on monotypes are monotypes)
    , rel Box   BoxBox      BoxBox      -- * -> ** : ☐☐ (type functions on polytypes are polytypes)
    ]

polarityOf :: Map (Name Expr) Expr -> Name Expr -> Expr -> M Polarity
polarityOf _ _ (Sort _) = return Constant
polarityOf _ n (Var x) | n == x    = return Positive
                       | otherwise = return Constant
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
typeOf _ (Sort c) = Sort <$> axiom c
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
        (Sort s1, Sort s2) -> case Map.lookup (s1, s2) relations of
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
        (Sort s1, Sort s2) -> case Map.lookup (s1, s2) relations of
            Nothing -> throwError "typeOf: pi relation violation"
            Just s3 -> return (Sort s3)
        _ -> throwError "typeOf: pi not sorts"

tof = runM . typeOf library

-- ERASURE

erase :: Map (Name Expr) Expr -> Expr -> M UExpr
erase m e@(Var n) = do
    case Map.lookup n m of
        Nothing -> throwError "erase: unbound variable"
        Just t -> do
            k <- typeOf m t
            let r = return (UVar (translate n))
            case k of
                Sort Star -> r
                Sort StarStar -> r
                _ -> throwError ("erase: non-computational variable " ++ ppshow e ++ " was not erased")
erase m (Lambda t z) = lunbind z $ \(n, e) -> do
    -- need to decide if it has computational content
    k <- typeOf m t
    case k of
        Sort Star -> ULambda . bind (translate n) <$> erase (Map.insert n t m) e
        Sort StarStar -> throwError "erase: lambda takes polytype as argument"
        _ -> erase (Map.insert n t m) e
erase m (App e1 e2) = do
    t <- typeOf m e2
    k <- typeOf m t
    let r = UApp <$> erase m e1 <*> erase m e2
    case k of
        Sort Star -> r
        Sort StarStar -> r
        _ -> erase m e1
erase _ (Pi _ _ _) = throwError "erase: pi has no computational content"
erase _ (Sort _) = throwError "erase: constant has no computational content"

erz = runM . erase library

-- TYPE INFERENCE

{-

What's going on here?

* We have an untyped lambda calculus UExpr. Ordinarily, typing this
  calculus would be straightforward. (Vanilla Hindley-Milner, and
  for any unresolved type variables, we just slap quantifiers on the
  front until it's good.  There is the somewhat delicate issue of
  let-polymorphism--we then have to muck around with quantifier
  instantiation--however, we're not including it in our language.)

* However, we have a global context which contains terms which are
  typed in the full language.  UExpr may refer to these terms, so
  we need to consider them appropriately.

* In rank-1 polymorphic calculus, this is still not a big deal;
  all such terms can be converted to prenex form, and then the
  variables introduced freshly as new things to bind to.

* However, we also have a typing context, which means some of the
  type variables are pre-bound in the environment, and should not
  be unified away.  Only variables under the quantifiers are fair
  game; the other variables are skolem variables.

-}

type GM = ErrorT String (FreshM)

runGM = either error id . runFreshM . runErrorT
upGM = either throwError return . runLFreshM . runErrorT

--  a local context 'm' (lets us do kind-checking)
--  a unification variable map (tells us how to translate bound variables)
--  global context is unnecessary; we can infer if a variable is free if
--  it's not in the unification variable map
--  INVARIANT: all types in global context are beta-normalized!
interpretAsHMType :: Map (Name Expr) Expr -> Map (Name Expr) (Name Type) -> Expr -> GM Type
interpretAsHMType _ _ (Sort _) = throwError ("tap: cannot interpret sort")
interpretAsHMType m u (Var n) = case Map.lookup n u of
    Just t -> return (TVar t)
    Nothing -> case Map.lookup n m of
        Just _ -> return (TSkolem n)
        Nothing -> throwError "tap: unbound variable"
interpretAsHMType m u (Pi _ ta z) = do
    (x, tb) <- unbind z
    t1 <- upGM $ typeOf m ta
    let m' = Map.insert x ta m
    t2 <- upGM $ typeOf m' tb
    let -- since arrows do not introduce new type variables, u is unmodified;
        -- in fact, lack of dependence states that any further types
        -- should type-check sans the annotation; we thus omit it and
        -- expect an unbound variable error if there actually was a
        -- problem
        starstar = TArr <$> interpretAsHMType m u ta <*> interpretAsHMType m u tb
        -- polymorphism! a fresh variable must be added
        boxstar = do t <- fresh (s2n "t")
                     interpretAsHMType m' (Map.insert x t u) tb
    case (t1, t2) of
        (Sort s1, Sort s2) -> case (s1, s2) of
            (Star, Star) -> starstar
            (Star, StarStar) -> starstar
            (Box, Star) -> boxstar
            (Box, StarStar) -> boxstar
            _ -> throwError ("tap: not implemented " ++ ppshow s1 ++ ", " ++ ppshow s2)
        _ -> throwError "tap: pi not sorts"
interpretAsHMType _ _ (Lambda _ _) = throwError "tap: illegal unnormalized lambda present in type"
interpretAsHMType m u (App t1 t2) = do
    k1 <- upGM $ typeOf m t1
    s1 <- upGM $ typeOf m k1
    case s1 of
        Sort Box -> return ()
        Sort BoxBox -> return ()
        _ -> throwError "tap: illegal kind"
    -- no attempt made at normalization; assumed already normalized, so
    -- must be an atomic TApp
    TApp <$> interpretAsHMType m u t1 <*> interpretAsHMType m u t2

constraintsOf :: Map (Name Expr) Expr -> UExpr -> GM ((Expr, Type), [(Type, Type)])
constraintsOf ctx = runWriterT . f Map.empty
    where f :: Map (Name UExpr) Type -> UExpr -> WriterT [(Type, Type)] GM (Expr, Type)
          f m (UVar n) = case Map.lookup n m of
            Just t -> return (Var (translate n), t)
            Nothing -> case Map.lookup (translate n) ctx of
                Just t -> do
                    -- notice that 'm' is irrelevant for HM types; this
                    -- is because we have no dependence on terms in the
                    -- types!
                    t' <- lift $ interpretAsHMType ctx Map.empty t
                    return (Var (translate n), t')
                Nothing -> throwError ("constraintsOf: unbound variable " ++ show n)
          f m (UApp e1 e2) = do
            (e1', t1) <- f m e1
            (e2', t2) <- f m e2
            t <- fresh (s2n "t")
            tell [(t1, TArr t2 (TVar t))]
            return (App e1' e2', (TVar t))
          f m (ULambda z) = do
            (x, e) <- unbind z
            t1 <- fresh (s2n "t")
            (e', t2) <- f (Map.insert x (TVar t1) m) e
            return (Lambda (Var (translate t1)) (bind (translate x) e'), TArr (TVar t1) t2)

rmap f x = fmap (\(a,b) -> (a, f b)) x
solve eq = f eq []
    where f eq s = case eq of
            [] -> return s
            ((t1, t2):eq') | t1 == t2 -> f eq' s
            ((TVar k, t):eq') | not (Set.member k (fv t)) ->
                let ts = subst k t
                in f (map (\(a,b) -> (ts a, ts b)) eq')
                     ((k,t):rmap ts s)
            ((t, TVar k):eq') | not (Set.member k (fv t)) ->
                let ts = subst k t
                in f (map (\(a,b) -> (ts a, ts b)) eq')
                     ((k,t):rmap ts s)
            ((TArr u1 v1, TArr u2 v2):eq') -> f ((u1,u2):(v1,v2):eq') s
            ((TApp u1 v1, TApp u2 v2):eq') -> f ((u1,u2):(v1,v2):eq') s
            _ -> throwError "Could not unify"

calculateQuantifiers uv cover =
    let uv' = Set.difference uv cover
        vs  = Set.intersection uv cover
        generate [] f = f
        -- this is wrong, need to infer kinds
        generate (x:xs) f = generate xs (\r -> Pi Unspecified (Sort Star) (bind (translate x) (f r)))
    in (uv', generate (Set.elems vs) id)

translateHMType :: Set (Name Type) -> Type -> GM Expr
translateHMType _ (TSkolem n) = return (Var n)
translateHMType uv (TVar n) = do
    let (uv', qs) = calculateQuantifiers uv (Set.singleton n)
    unless (Set.null uv') $ throwError "translateHMType: bug! free variables never showed up!"
    return (qs (Var (translate n)))
translateHMType uv (TArr t1 t2) = do
    x <- fresh (s2n "_")
    let (uv', qs) = calculateQuantifiers uv (fv t1)
    e1 <- translateHMType uv' t1
    e2 <- translateHMType uv' t2
    return (qs (Pi Unspecified e1 (bind x e2)))
translateHMType uv (TApp t1 t2) = do
    let (uv', qs) = calculateQuantifiers uv (Set.union (fv t1) (fv t2))
    e1 <- translateHMType uv' t1
    e2 <- translateHMType uv' t2
    return (qs (App e1 e2))

inferType :: Map (Name Expr) Expr -> UExpr -> GM Expr
inferType ctx e = do
    ((_, t), eq) <- constraintsOf ctx e
    subs <- solve eq
    let t' = substs subs t
    translateHMType (fv t') t'

infer = runGM . inferType library

{-
elaborate :: Map (Name Expr) Expr -> UExpr -> GM Expr
elaborate ctx e = do
    ((e, _), eq) <- constraintsOf ctx e
    subs <- solve eq
    return (substs subs e)

elab = runGM . elaborate library
-}

-- PRETTY PRINTING

class Pretty p where
    ppr :: (Applicative m, LFresh m) => Int -> p -> m Doc

pprint = putStrLn . ppshow
ppshow = PP.render . runLFreshM . ppr 0

instance Pretty Sort where
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
pprPolarity Constant = return $ PP.text "°"
pprPolarity Unspecified = return $ PP.text "±"

nopEq x y = if x == y then return (PP.text "") else ppr 0 y

instance Pretty Expr where
    ppr _ (Var n) = return (PP.text (show n))
    ppr _ (Sort c) = ppr 0 c
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
star = Sort Star
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
