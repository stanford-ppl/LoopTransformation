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

class Pretty p where
    ppr :: (Applicative m, LFresh m) => Int -> p -> m Doc

-- warning: Ord is so that it is mappable; but this has LATTICE structure
-- Unspecified > Positive > Constant
--             > Negative >
data Polarity = Unspecified | Positive | Negative | Constant
    deriving (Show, Eq)

data Kind = KType
          | KArr {- Polarity -} Kind Kind
    deriving (Show)

var :: String -> Expr
var = Var . string2Name

tvar :: String -> Type
tvar = TVar . string2Name

instance Pretty Kind where
    ppr _ KType = return (PP.text "★")
    ppr p (KArr k1 k2) = prettyParen (p > 0) <$> (parr <$> ppr 0 k1 <*> ppr 1 k2)

pprint = runLFreshM . ppr 0
parr a b = a <+> PP.text "→" <+> b
prettyParen True = PP.parens
prettyParen False = id
pbind b n k e = PP.text b <> PP.parens (PP.text (show n) <+> PP.colon <+> k) <> PP.text "." <+> e

-- mu/fold/roll come from the Haskell tradition
-- PFPL calls these ind/rec/fold
-- Coq calls these Inductive/fix/_

data Type = TVar (Name Type)
          | TArr Type Type
          | TLambda Kind (Bind (Name Type) Type)
          | TApp Type Type
          | TMu Type
          | TForall Type
    deriving (Show)

pbinds p c k b = fmap (prettyParen (p > 0)) . lunbind b $ \(n,t) ->
    pbind c n <$> ppr 0 k <*> ppr 0 t
pbinder p c (TLambda k b) = pbinds p c k b
pbinder p c t = prettyParen (p > 0) <$> ((PP.text c <+>) <$> ppr 1 t)
papp p t1 t2 = prettyParen (p > 1) <$> ((<+>) <$> ppr 1 t1 <*> ppr 2 t2)

instance Pretty Type where
    ppr _ (TVar n) = return (PP.text (show n))
    ppr p (TArr t1 t2) = prettyParen (p > 0) <$> (parr <$> ppr 1 t1 <*> ppr 0 t2)
    ppr p (TForall t) = pbinder p "∀" t
    ppr p (TMu t) = pbinder p "μ" t
    ppr p (TLambda k b) = pbinds p "Λ" k b
    ppr p (TApp t1 t2) = papp p t1 t2

data Expr = Var (Name Expr)
          | Lambda Type (Bind (Name Expr) Expr)
          | App Expr Expr
          | TyLambda Kind (Bind (Name Type) Expr)
          | TyApp Expr Type
          | Fold Expr Expr
          | Roll Type Expr
    deriving (Show)

instance Pretty Expr where
    ppr _ (Var n) = return (PP.text (show n))
    ppr p (Lambda t b) = pbinds p "λ" t b
    ppr p (App e1 e2) = papp p e1 e2
    ppr p (TyLambda k b) = pbinds p "Λ" k b
    ppr p (TyApp e t) = papp p e t
    ppr p (Fold e1 e2) = ppr p (App (App (var "fold") e1) e2)
    ppr p (Roll t e) = ppr p (App (TyApp (var "roll") t) e)

$(derive [''Type, ''Expr, ''Kind])
instance Alpha Kind
instance Alpha Type
instance Alpha Expr
instance Subst Expr Expr where
    isvar (Var v) = Just (SubstName v)
    isvar _ = Nothing
instance Subst Expr Type where
instance Subst Expr Kind where
instance Subst Type Type where
    isvar (TVar v) = Just (SubstName v)
    isvar _ = Nothing
instance Subst Type Kind where

done :: MonadPlus m => m a
done = mzero

mpbind f b = do
    (x, t) <- unbind b
    t' <- f t
    return (bind x t')

type M = FreshM

-- Note: looks INSIDE binders! (might be kind of inefficient)
beta :: Type -> MaybeT M Type
beta (TVar _) = done
beta (TArr t1 t2) =
        TArr <$> beta t1 <*> pure t2
    <|> TArr <$> pure t1 <*> beta t2
beta (TLambda k b) =
        TLambda k <$> mpbind beta b
beta (TApp (TLambda _ b) t2) = do
        (n, t1) <- unbind b
        return $ subst n t2 t1
beta (TApp t1 t2) =
        TApp <$> beta t1 <*> pure t2
    <|> TApp <$> pure t1 <*> beta t2
beta (TMu t) = TMu <$> beta t
beta (TForall t) = TForall <$> beta t

normalize :: Type -> M Type
normalize t = do
    m <- runMaybeT (beta t)
    case m of
        Just t' -> normalize t'
        Nothing -> return t

kindOf :: Map (Name Type) Kind -> Type -> M Kind
kindOf m (TVar n) = maybe (error "kindOf: unbound variable") return (Map.lookup n m)
kindOf m (TLambda k p) = do
    (n, t) <- unbind p
    KArr k <$> kindOf (Map.insert n k m) t
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
        KArr k11 k12 | k11 `aeq` k2 -> return k12
                     | otherwise -> error ("kindOf: could not unify " ++ show k11 ++ " and " ++ show k2)
        _ -> error "kindOf: attempt to apply to non-arrow kind"
kindOf m (TMu t) = do
    k <- kindOf m t
    case k of
        KArr k1 k2 | k1 `aeq` k2 -> return k1 -- perhaps we shouldn't be polymorphic
                   | otherwise -> error "kindOf: cannot take fixpoint of non-endomorphic operator"
        _ -> error "kindOf: cannot take fixpoint of *"
kindOf m (TForall t) = do
    k <- kindOf m t
    case k of
        KArr _ k2 -> return k2
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
    return (TForall (TLambda k (bind n t)))
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

lam :: Type -> String -> Expr -> Expr
lam t x e = Lambda t $ bind (string2Name x) e

tlam :: Kind -> String -> Expr -> Expr
tlam k x e = TyLambda k $ bind (string2Name x) e

tylam :: Kind -> String -> Type -> Type
tylam k x t = TLambda k $ bind (string2Name x) t

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

infixl 9 #, &
infixr 1 ~>

(&) = TyApp

class SynApp a where (#) :: a -> a -> a
instance SynApp Expr where (#) = App
instance SynApp Type where (#) = TApp

class SynArr a where (~>) :: a -> a -> a
instance SynArr Type where (~>) = TArr
instance SynArr Kind where (~>) = KArr

instance IsString Expr where fromString = var
instance IsString Type where fromString = tvar
