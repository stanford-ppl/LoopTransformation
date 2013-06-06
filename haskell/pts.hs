
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
          | Pole
    deriving (Show, Ord, Eq)

data VarInfo = Skolem | Unification
    deriving (Show)

data Expr = Sort Sort
          | Polarity Polarity
          | Var VarInfo (Name Expr)
          | App Expr Expr
          | Lambda Expr (Bind (Name Expr) Expr)
          | Pi {- polarity -} Expr Expr (Bind (Name Expr) Expr)
    deriving (Show)

-- FRONTEND LANGUAGE

data UExpr = UVar (Name UExpr)
           | UApp UExpr UExpr
           | ULambda (Bind (Name UExpr) UExpr)
    deriving (Show)

-- UNBOUND NONSENSE

$(derive [''Expr, ''Sort, ''Polarity, ''VarInfo])
$(derive [''UExpr])
instance Alpha Expr
instance Alpha Sort
instance Alpha UExpr
instance Alpha Polarity
instance Alpha VarInfo
instance Subst Expr Sort where
instance Subst Expr VarInfo where
instance Subst Expr Polarity where
instance Subst Expr Expr where
    isvar (Var _ v) = Just (SubstName v)
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

polaritySubtypeOf a b = lub a b == b

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
beta (Var _ _) = done
beta (Sort _) = done
beta (Polarity _) = done
beta (Pi p t z) = lunbind z $ \(x, e) ->
        Pi <$> beta p <*> pure t <*> pure (bind x e)
    <|> Pi <$> pure p <*> beta t <*> pure (bind x e)
    <|> Pi <$> pure p <*> pure t <*> fmap (bind x) (beta e)
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
axiom Pole = throwError "axiom: pole is not typeable"

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
polarityOf _ _ (Polarity _) = throwError "polarityOf: illegal polarity"
polarityOf _ n (Var Skolem x) | n == x    = return Positive
                              | otherwise = return Constant
polarityOf _ _ (Var Unification _) = throwError "polarityOf: illegal unification variable"
polarityOf m n (App t1 t2) = do
    k <- typeOf m t1
    p1 <- polarityOf m n t1
    p2 <- polarityOf m n t2
    case k of
        Pi (Polarity p) _ _ -> return (lub p1 (p * p2))
        Pi _ _ _ -> throwError ("polarityOf: ill-typed pi")
        _ -> throwError ("polarityOf: attempting to apply non-pi type")
polarityOf m n (Lambda t z) = lunbind z $ \(x, e) -> do
    if Set.member n (fv t)
        then return Unspecified -- conservative choice
        else polarityOf (Map.insert x t m) n e
polarityOf m n (Pi _ t1 z) = lunbind z $ \(x, t2) -> do
    p1 <- polarityOf m n t1
    p2 <- polarityOf (Map.insert x t1 m) n t2
    return (lub (-p1) p2)

-- implement this with erasure
{-
erasePolarity = runWriterT . runM . f
    where f e@(Sort _) = return e
          f (Polarity _) = Var Unification <$> lfresh (s2n "t")

subtypeOf :: Expr -> Expr -> Bool
e1 `subtypeOf` e2 =
    let (e1', p1) = erasePolarity e1
        (e2', p2) = erasePolarity e2'
    in (e1' `aeq` e2') && and (zipWith polaritySubtypeOf p1 p2)
    -}

typeOf :: Map (Name Expr) Expr -> Expr -> M Expr
typeOf _ (Sort c) = Sort <$> axiom c
typeOf _ (Polarity _) = return (Sort Pole)
typeOf m (Var Skolem n) = maybe (throwError ("typeOf: unbound variable " ++ show n)) return (Map.lookup n m)
typeOf _ (Var Unification _) = throwError "typeOf: illegal unification variable"
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
                return (Pi (Polarity p) ta (bind x tb))
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
erase m e@(Var Skolem n) = do
    case Map.lookup n m of
        Nothing -> throwError "erase: unbound variable"
        Just t -> do
            k <- typeOf m t
            let r = return (UVar (translate n))
            case k of
                Sort Star -> r
                Sort StarStar -> r
                _ -> throwError ("erase: non-computational variable " ++ ppshow e ++ " was not erased")
erase _ (Var Unification _) = throwError "error: illegal unification variable"
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
erase _ (Polarity _) = throwError "erase: polarity has no computational content"

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
interpretAsHMType :: Map (Name Expr) Expr -> Set (Name Expr) -> Expr -> GM Expr
interpretAsHMType _ _ (Sort _) = throwError ("tap: cannot interpret sort")
interpretAsHMType _ _ (Polarity _) = throwError ("tap: cannot interpret polarity")
interpretAsHMType m _ e@(Var Skolem n) | Map.member n m = return e
                                       | otherwise = throwError "tap: unbound skolem variable"
interpretAsHMType _ u e@(Var Unification n) | Set.member n u = return e
                                            | otherwise = throwError "tap: unbound unification variable"
interpretAsHMType m u (Pi _ ta z) = do
    -- polarity at type level is meaningless; ignore it
    (x, tb) <- unbind z
    t1 <- upGM $ typeOf m ta
    let m' = Map.insert x ta m
    t2 <- upGM $ typeOf m' tb
    let -- since arrows do not introduce new type variables, u is unmodified;
        -- in fact, lack of dependence states that any further types
        -- should type-check sans the annotation; we thus omit it and
        -- expect an unbound variable error if there actually was a
        -- problem
        starstar = Pi (Polarity Unspecified) <$> interpretAsHMType m u ta <*> fmap (bind x) (interpretAsHMType m u tb)
        -- polymorphism! a fresh variable must be added
        boxstar = do t <- fresh (s2n "t")
                     interpretAsHMType m' (Set.insert t u) tb
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
    App <$> interpretAsHMType m u t1 <*> interpretAsHMType m u t2

constraintsOf :: Map (Name Expr) Expr -> UExpr -> GM ((Expr, Expr), [(Expr, Expr)])
constraintsOf ctx = runWriterT . f Map.empty
    where f :: Map (Name UExpr) Expr -> UExpr -> WriterT [(Expr, Expr)] GM (Expr, Expr)
          f m (UVar n) = case Map.lookup n m of
            Just t -> return (Var Skolem (translate n), t)
            Nothing -> case Map.lookup (translate n) ctx of
                Just t -> do
                    -- notice that 'm' is irrelevant for HM types; this
                    -- is because we have no dependence on terms in the
                    -- types!
                    t' <- lift $ interpretAsHMType ctx Set.empty t
                    return (Var Skolem (translate n), t')
                Nothing -> throwError ("constraintsOf: unbound variable " ++ show n)
          f m (UApp e1 e2) = do
            (e1', t1) <- f m e1
            (e2', t2) <- f m e2
            t <- Var Unification <$> fresh (s2n "t")
            x <- fresh (s2n "_")
            tell [(t1, Pi (Polarity Unspecified) t2 (bind x t))]
            return (App e1' e2', t)
          f m (ULambda z) = do
            (x, e) <- unbind z
            t1 <- Var Unification <$> fresh (s2n "t")
            (e', t2) <- f (Map.insert x t1 m) e
            return (Lambda t1 (bind (translate x) e'), Pi (Polarity Unspecified) t1 (bind (translate x) t2))

rmap f x = fmap (\(a,b) -> (a, f b)) x
solve eq = f eq []
    where f eq s = case eq of
            [] -> return s
            ((t1, t2):eq') | t1 `aeq` t2 -> f eq' s
            ((Var Unification k, t):eq') | not (Set.member k (fv t)) ->
                let ts = subst k t
                in f (map (\(a,b) -> (ts a, ts b)) eq')
                     ((k,t):rmap ts s)
            ((t, Var Unification k):eq') | not (Set.member k (fv t)) ->
                let ts = subst k t
                in f (map (\(a,b) -> (ts a, ts b)) eq')
                     ((k,t):rmap ts s)
            ((Pi (Polarity p1) u1 z1, Pi (Polarity p2) u2 z2):eq') | p1 == p2 -> do
                Just (_, v1, _, v2) <- unbind2 z1 z2
                f ((u1,u2):(v1,v2):eq') s
            ((App u1 v1, App u2 v2):eq') -> f ((u1,u2):(v1,v2):eq') s
            ((Lambda t1 z1, Lambda t2 z2):eq') -> do
                Just (_, e1, _, e2) <- unbind2 z1 z2
                f ((t1,t2):(e1,e2):eq') s
            _ -> throwError "Could not unify"

calculateQuantifiers uv cover = do
    let uv' = Set.difference uv cover
        vs  = Set.intersection uv cover
        generate [] f = return f
        generate (x:xs) f = do
            k <- Var Unification <$> fresh (s2n "k")
            generate xs (\r -> Pi (Polarity Unspecified) k (bind (translate x) (f r)))
    qs <- generate (Set.elems vs) id
    return (uv', qs)

translateHMType :: Set (Name Expr) -> Expr -> WriterT [(Expr, Expr)] GM Expr
translateHMType _ (Sort _) = throwError "translateHMType: bug! sort"
translateHMType _ (Polarity _) = throwError "translateHMType: bug! polarity"
translateHMType _ (Lambda _ _) = throwError "translateHMType: bug! lambda"
translateHMType _ e@(Var Skolem _) = return e
translateHMType uv (Var Unification n) = do
    (uv', qs) <- calculateQuantifiers uv (Set.singleton n)
    unless (Set.null uv') $ throwError "translateHMType: bug! free variables never showed up!"
    return (qs (Var Skolem (translate n)))
translateHMType uv (Pi p t1 z) = do
    (x, t2) <- unbind z
    (uv', qs) <- calculateQuantifiers uv (fv t1)
    e1 <- translateHMType uv' t1
    e2 <- translateHMType uv' t2
    return (qs (Pi p e1 (bind x e2)))
translateHMType uv (App t1 t2) = do
    (uv', qs) <- calculateQuantifiers uv (Set.union (fv t1) (fv t2))
    e1 <- translateHMType uv' t1
    e2 <- translateHMType uv' t2
    ut <- Var Unification <$> fresh (s2n "k")
    -- tell [(ut, Pi Unspecified)]
    return (qs (App e1 e2))

inferType :: Map (Name Expr) Expr -> UExpr -> GM Expr
inferType ctx e = do
    ((_, t), eq) <- constraintsOf ctx e
    subs <- solve eq
    let t' = substs subs t
    (t'', eq'') <- runWriterT $ translateHMType (Set.difference (fv t') (Map.keysSet ctx)) t'
    return t''

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
    ppr _ Pole = return (PP.text "Pole")

instance Pretty Polarity where
    ppr _ = pprPolarity
    -- ppr _ = pprNop

pprNop _ = return $ PP.text ""
pprPolarity Positive = return $ PP.text "⁺"
pprPolarity Negative = return $ PP.text "⁻"
pprPolarity Constant = return $ PP.text "°"
pprPolarity Unspecified = return $ PP.text "±"

nopEq x y = if x `aeq` y then return (PP.text "") else ppr 0 y

instance Pretty Expr where
    ppr _ (Polarity p) = ppr 0 p
    ppr _ (Var Skolem n) = return (PP.text (show n))
    ppr _ (Var Unification n) = return (PP.text "?" <> PP.text (show n))
    ppr _ (Sort c) = ppr 0 c
    ppr p (Lambda t z) = pbinds p "λ" t z
    -- not perfect: want to look at the sorts to get a better idea for
    -- how to print it...
    ppr p (Pi pm t z) = fmap (prettyParen (p > 0)) . lunbind z $ \(x, e) -> do
        if Set.member x (fv e)
            then pbind "Π" x <$> nopEq (Polarity Unspecified) pm <*> ppr 0 t <*> ppr 0 e
            else parr' <$> ppr 0 t <*> nopEq (Polarity Positive) pm <*> ppr 0 e
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
forall x t e = Pi (Polarity Positive) t $ bind (string2Name x) e
(#) = App
a ~> b = Pi (Polarity Positive) a $ bind (s2n "_") b
star = Sort Star
phi f1 f2 = forall "a" star (f1 # "a" ~> f2 # "a")

instance IsString Expr where fromString = Var Skolem . fromString
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
