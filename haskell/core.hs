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
import Control.Monad.Trans.Maybe
import Control.Applicative
import Control.Monad
import qualified Text.PrettyPrint as PP
import Text.PrettyPrint (Doc, (<+>), (<>))
import Data.String

-- * Implementation of polarity is as described in Martin Steffen's
--   thesis, but with subtyping omitted (we use the stratified kind
--   system.)
-- * Typing rules for inductive data types were lifted from PFPL, but
--   without the strict positivity requirement.

-- DATA TYPES

-- Bob Harper suggests that one should distinguish from a data type
-- and the functor associated with it
data Polarity = Unspecified | Positive | Negative | Constant
    deriving (Show)

data Kind = KType
          | KArr Polarity Kind Kind
    deriving (Show)

data Type = TVar (Name Type)
          | TArr Type Type
          | TLambda Kind (Bind (Name Type) Type)
          | TApp Type Type
          | TMu Type
          | TForall Type
    deriving (Show)

data Expr = Var (Name Expr)
          | Lambda Type (Bind (Name Expr) Expr)
          | App Expr Expr
          | TyLambda Kind (Bind (Name Type) Expr)
          | TyApp Expr Type
          | Fold Expr Expr
          | Roll Type Expr
    deriving (Show)

-- UNBOUND NONSENSE

$(derive [''Type, ''Expr, ''Kind, ''Polarity])

instance Alpha Kind
instance Alpha Type
instance Alpha Expr
instance Alpha Polarity

instance Subst Expr Expr where
    isvar (Var v) = Just (SubstName v)
    isvar _ = Nothing
instance Subst Type Type where
    isvar (TVar v) = Just (SubstName v)
    isvar _ = Nothing
instance Subst Expr Type where
instance Subst Expr Kind where
instance Subst Expr Polarity where
instance Subst Type Kind where
instance Subst Type Polarity where

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

type M = FreshM

-- EVALUATION AND TYPE CHECKING

-- Note: looks INSIDE binders!
beta :: Type -> MaybeT M Type
beta (TVar _) = done
beta (TArr t1 t2) =
        TArr <$> beta t1 <*> pure t2
    <|> TArr <$> pure t1 <*> beta t2
beta (TLambda k b) = do
        (x, t) <- unbind b
        t' <- beta t
        return (TLambda k (bind x t'))
beta (TApp (TLambda _ b) t2) = do
        (n, t1) <- unbind b
        return $ subst n t2 t1
beta (TApp t1 t2) =
        TApp <$> beta t1 <*> pure t2
    <|> TApp <$> pure t1 <*> beta t2
beta (TMu t) = TMu <$> beta t
beta (TForall t) = TForall <$> beta t

-- More efficient technique is "normalization by evaluation"
--   described at http://math.andrej.com/2012/11/11/how-to-implement-dependent-type-theory-ii/
normalize :: Type -> M Type
normalize t = do
    m <- runMaybeT (beta t)
    case m of
        Just t' -> normalize t'
        Nothing -> return t

polarityOf :: Map (Name Type) Kind -> Name Type -> Type -> M Polarity
polarityOf _ x (TVar n) | n == x    = return Positive
                        | otherwise = return Constant
polarityOf m x (TArr t1 t2) = do
    p1 <- polarityOf m x t1
    p2 <- polarityOf m x t2
    return (lub (-p1) p2)
polarityOf m x (TLambda k b) = do
    (n, t) <- unbind b
    polarityOf (Map.insert n k m) x t
polarityOf m x (TApp t1 t2) = do
    k <- kindOf m t1
    p1 <- polarityOf m x t1
    p2 <- polarityOf m x t2
    case k of
        KArr p _ _ -> return (lub p1 (p * p2))
        _ -> error "polarityOf: ill-kinded type application"
polarityOf m x (TMu t) = polarityOf m x t -- I hope this is right!
polarityOf m x (TForall t) = polarityOf m x t

kindOf :: Map (Name Type) Kind -> Type -> M Kind
kindOf m (TVar n) = maybe (error "kindOf: unbound variable") return (Map.lookup n m)
kindOf m (TLambda k p) = do
    (n, t) <- unbind p
    let m' = Map.insert n k m
    p <- polarityOf m' n t
    KArr p k <$> kindOf m' t
kindOf m (TArr t1 t2) = do
    k1 <- kindOf m t1
    unless (k1 `aeq` KType) $ error "kindOf: ill-kinded left argument of type arrow"
    k2 <- kindOf m t2
    unless (k2 `aeq` KType) $ error "kindOf: ill-kinded right arguemnt of type arrow"
    return KType
kindOf m (TApp t1 t2) = do
    k1 <- kindOf m t1
    k2 <- kindOf m t2
    case k1 of
        KArr _ k11 k12 | k11 `aeq` k2 -> return k12
                       | otherwise -> error ("kindOf: could not unify " ++ show k11 ++ " and " ++ show k2)
        _ -> error "kindOf: attempt to apply to non-arrow kind"
kindOf m (TMu t) = do
    k <- kindOf m t
    case k of
        KArr Positive k1 k2 | k1 `aeq` k2 -> return k1 -- perhaps we shouldn't be polymorphic
                            | otherwise -> error "kindOf: cannot take fixpoint of non-endomorphic operator"
        KArr _ _ _ -> error "kindOf: cannot take fixpoint of non-positive operator"
        _ -> error "kindOf: cannot take fixpoint of *"
kindOf m (TForall t) = do
    k <- kindOf m t
    case k of
        KArr _ _ k2 -> return k2
        _ -> error "kindOf: cannot universally quantify over *"

kof = runFreshM . kindOf Map.empty
tof = runFreshM . typeOf Map.empty Map.empty

typeOf :: Map (Name Type) Kind -> Map (Name Expr) Type -> Expr -> M Type
typeOf km m e = do
    t <- typeOf' km m e
    kindOf km t -- sanity
    normalize t

typeOf' :: Map (Name Type) Kind -> Map (Name Expr) Type -> Expr -> M Type
typeOf' _ m (Var n) = maybe (error "typeOf: unbound variable") return (Map.lookup n m)
typeOf' km m (Lambda t b) = do
    k <- kindOf km t
    unless (k `aeq` KType) $ error "typeOf: lambda type annotation is not *"
    (n, e) <- unbind b
    TArr t <$> typeOf km (Map.insert n t m) e
typeOf' km m (TyLambda k b) = do
    (n, e) <- unbind b
    t <- typeOf (Map.insert n k km) m e
    return (TForall (TLambda k (bind n t))) -- note the forall!
typeOf' km m (App e1 e2) = do
    t1 <- typeOf km m e1
    t2 <- typeOf km m e2
    case t1 of
        TArr t11 t12 | t11 `aeq` t2 -> return t12
                     | otherwise -> error ("typeOf: could not unify " ++ show t1 ++ " and " ++ show t2)
        _ -> error "typeOf: attempt to apply to non-function type"
typeOf' km m (TyApp e t) = do
    nt <- typeOf km m e
    k' <- kindOf km t
    case nt of
        TForall (TLambda k b)
            | k `aeq` k' -> do
                (n, t') <- unbind b
                return (subst n t t')
            | otherwise -> error ("typeOf: could not unify kinds " ++ show k ++ " and " ++ show k')
        _ -> error "typeOf: cannot apply to non-universal quantifier"
typeOf' km m (Fold e1 e2) = do
    ta <- typeOf km m e1
    tb <- typeOf km m e2
    case (ta, tb) of
        (TArr t1 t1', TMu t2) -> do
            t2' <- normalize (TApp t2 t1')
            unless (t1 `aeq` t2') $ error ("typeOf: could not unify " ++ show t1 ++ " and " ++ show t2 ++ " applied to " ++ show t1')
            return t1'
        _ -> error "typeOf: folder must be a function"
typeOf' km m (Roll t e) = do
    ta <- typeOf km m e
    ta' <- normalize (TApp t (TMu t))
    unless (ta `aeq` ta') $ error "typeOf: cannot unify for roll"
    return (TMu t)

-- PRETTY PRINTING

class Pretty p where
    ppr :: (Applicative m, LFresh m) => Int -> p -> m Doc

pprint = runLFreshM . ppr 0

instance Pretty Polarity where
    ppr _ Positive = return $ PP.text "⁺"
    ppr _ Negative = return $ PP.text "⁻"
    ppr _ Constant = return $ PP.text "°"
    ppr _ Unspecified = return $ PP.text "±"

instance Pretty Kind where
    ppr _ KType = return (PP.text "★")
    ppr p (KArr po k1 k2) = prettyParen (p > 0) <$> (parr' <$> ppr 0 k1 <*> ppr 0 po <*> ppr 1 k2)

instance Pretty Type where
    ppr _ (TVar n) = return (PP.text (show n))
    ppr p (TArr t1 t2) = prettyParen (p > 0) <$> (parr <$> ppr 1 t1 <*> ppr 0 t2)
    ppr p (TForall t) = pbinder p "∀" t
    ppr p (TMu t) = pbinder p "μ" t
    ppr p (TLambda k b) = pbinds p "Λ" k b
    ppr p (TApp t1 t2) = papp p t1 t2

instance Pretty Expr where
    ppr _ (Var n) = return (PP.text (show n))
    ppr p (Lambda t b) = pbinds p "λ" t b
    ppr p (App e1 e2) = papp p e1 e2
    ppr p (TyLambda k b) = pbinds p "Λ" k b
    ppr p (TyApp e t) = papp p e t
    ppr p (Fold e1 e2) = ppr p (App (App (var "fold") e1) e2)
    ppr p (Roll t e) = ppr p (App (TyApp (var "roll") t) e)

parr' a b c = a <+> PP.text "→" <> b <+> c
parr a b = a <+> PP.text "→" <+> b
prettyParen True = PP.parens
prettyParen False = id
pbind b n k e = PP.text b <> PP.parens (PP.text (show n) <+> PP.colon <+> k) <> PP.text "." <+> e
pbinds p c k b = fmap (prettyParen (p > 0)) . lunbind b $ \(n,t) ->
    pbind c n <$> ppr 0 k <*> ppr 0 t
pbinder p c (TLambda k b) = pbinds p c k b
pbinder p c t = prettyParen (p > 0) <$> ((PP.text c <+>) <$> ppr 1 t)
papp p t1 t2 = prettyParen (p > 1) <$> ((<+>) <$> ppr 1 t1 <*> ppr 2 t2)

-- EXAMPLE SUPPORT CODE

infixl 9 #, &
infixr 1 ~>

(&) = TyApp
lam t x e = Lambda t $ bind (string2Name x) e
tlam k x e = TyLambda k $ bind (string2Name x) e
tylam k x t = TLambda k $ bind (string2Name x) t
var = Var . string2Name
tvar = TVar . string2Name

class SynApp a where (#) :: a -> a -> a
instance SynApp Expr where (#) = App
instance SynApp Type where (#) = TApp

class SynArr a where (~>) :: a -> a -> a
instance SynArr Type where (~>) = TArr
instance SynArr Kind where (~>) = KArr Positive -- a "reasonable" default

instance IsString Expr where fromString = var
instance IsString Type where fromString = tvar

-- EXAMPLES

exIdentity = tlam KType "a"
           . lam "a" "x"
           $ var "x"

exFold = tlam KType "r"
       . tlam (KType ~> KType) "f"
       . lam ("f" # "r" ~> "r") "f"
       . lam (TMu "f") "xs"
       $ Fold "f" "xs"

exRoll = tlam (KType ~> KType) "natf"
       . lam (TMu "natf") "n"
       . lam (TForall (tylam KType "n" ("n" ~> "natf" # "n"))) "succ"
       $ Roll "natf" ("succ" & TMu "natf" # "n")


