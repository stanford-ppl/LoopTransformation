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
import Control.Monad.Error
import qualified Text.PrettyPrint as PP
import Text.PrettyPrint (Doc, (<+>), (<>))
import Data.String
-- import Debug.Trace

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

type M = ErrorT String LFreshM

-- EVALUATION AND TYPE CHECKING

-- Note: looks INSIDE binders!
beta :: Type -> MaybeT M Type
beta (TVar _) = done
beta (TArr t1 t2) =
        TArr <$> beta t1 <*> pure t2
    <|> TArr <$> pure t1 <*> beta t2
beta (TLambda k b) = do
        lunbind b $ \(x, t) -> do
        t' <- beta t
        return (TLambda k (bind x t'))
beta (TApp (TLambda _ b) t2) = do
        lunbind b $ \(n, t1) -> do
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
    lunbind b $ \(n, t) -> do
    polarityOf (Map.insert n k m) x t
polarityOf m x (TApp t1 t2) = do
    k <- kindOf m t1
    p1 <- polarityOf m x t1
    p2 <- polarityOf m x t2
    case k of
        KArr p _ _ -> return (lub p1 (p * p2))
        _ -> throwError ("polarityOf: ill-kinded type application of " ++ ppshow t1 ++ " and " ++ ppshow t2)
polarityOf m x (TMu t) = polarityOf m x t -- I hope this is right!
polarityOf m x (TForall t) = polarityOf m x t

kindOf :: Map (Name Type) Kind -> Type -> M Kind
kindOf m (TVar n) = maybe (throwError "kindOf: unbound variable") return (Map.lookup n m)
kindOf m (TLambda k p) = do
    lunbind p $ \(n, t) -> do
    let m' = Map.insert n k m
    p <- polarityOf m' n t
    KArr p k <$> kindOf m' t
kindOf m (TArr t1 t2) = do
    k1 <- kindOf m t1
    unless (k1 `aeq` KType) $ throwError "kindOf: ill-kinded left argument of type arrow"
    k2 <- kindOf m t2
    unless (k2 `aeq` KType) $ throwError "kindOf: ill-kinded right arguemnt of type arrow"
    return KType
kindOf m (TApp t1 t2) = do
    k1 <- kindOf m t1
    k2 <- kindOf m t2
    case k1 of
        KArr _ k11 k12 | k11 `aeq` k2 -> return k12
                       | otherwise -> throwError ("kindOf: could not unify " ++ ppshow k11 ++ " and " ++ ppshow k2)
        _ -> throwError ("kindOf: attempt to apply to non-arrow kind " ++ ppshow t1 ++ " : " ++ ppshow k1)
kindOf m (TMu t) = do
    k <- kindOf m t
    case k of
        KArr Positive k1 k2 | k1 `aeq` k2 -> return k1
                            | otherwise -> throwError "kindOf: cannot take fixpoint of non-endomorphic operator"
        KArr _ _ _ -> throwError "kindOf: cannot take fixpoint of non-positive operator"
        _ -> throwError ("kindOf: cannot take fixpoint of " ++ ppshow k)
kindOf m (TForall t) = do
    k <- kindOf m t
    case k of
        KArr _ _ k2 -> return k2
        _ -> throwError ("kindOf: cannot universally quantify over " ++ ppshow k)

-- what this ordering I don't
kof = runLFreshM . runErrorT . kindOf Map.empty
tof = runLFreshM . runErrorT . typeOf Map.empty Map.empty

typeOf :: Map (Name Type) Kind -> Map (Name Expr) Type -> Expr -> M Type
typeOf km m e = do
    t <- typeOf' km m e
    kindOf km t -- sanity
    normalize t

typeOf' :: Map (Name Type) Kind -> Map (Name Expr) Type -> Expr -> M Type
typeOf' _ m (Var n) = maybe (throwError ("typeOf: unbound variable " ++ show n)) return (Map.lookup n m)
typeOf' km m (Lambda t b) = do
    k <- kindOf km t
    unless (k `aeq` KType) $ throwError "typeOf: lambda type annotation is not *"
    lunbind b $ \(n, e) -> do
    TArr t <$> typeOf km (Map.insert n t m) e
typeOf' km m (TyLambda k b) = do
    lunbind b $ \(n, e) -> do
    t <- typeOf (Map.insert n k km) m e
    return (TForall (TLambda k (bind n t))) -- note the forall!
typeOf' km m (App e1 e2) = do
    t1 <- typeOf km m e1
    t2 <- typeOf km m e2
    case t1 of
        TArr t11 t12 | t11 `aeq` t2 -> return t12
                     | otherwise -> throwError ("typeOf: could not apply (" ++ ppshow e1 ++ " : " ++ ppshow t1 ++ ") and (" ++ ppshow e2 ++ " : " ++ ppshow t2 ++ ")")
        _ -> throwError "typeOf: attempt to apply to non-function type"
typeOf' km m (TyApp e t) = do
    nt <- typeOf km m e
    k' <- kindOf km t
    case nt of
        TForall (TLambda k b)
            | k `aeq` k' -> do
                lunbind b $ \(n, t') -> return (subst n t t')
            | otherwise -> throwError ("typeOf: could not unify kinds " ++ ppshow k ++ " and " ++ ppshow k')
        _ -> throwError "typeOf: cannot apply to non-universal quantifier"
typeOf' km m (Fold e1 e2) = do
    ta <- typeOf km m e1
    tb <- typeOf km m e2
    case (ta, tb) of
        (TArr t1 t1', TMu t2) -> do
            t2' <- normalize (TApp t2 t1')
            unless (t1 `aeq` t2') $ throwError ("typeOf: could not unify " ++ ppshow t1 ++ " and " ++ ppshow t2 ++ " applied to " ++ ppshow t1')
            return t1'
        _ -> throwError "typeOf: folder must be a function"
typeOf' km m (Roll t e) = do
    ta <- typeOf km m e
    ta' <- normalize (TApp t (TMu t))
    unless (ta `aeq` ta') $ throwError "typeOf: cannot unify for roll"
    return (TMu t)

-- PRETTY PRINTING

class Pretty p where
    ppr :: (Applicative m, LFresh m) => Int -> p -> m Doc

pprint = putStrLn . ppshow
ppshow = PP.render . runLFreshM . ppr 0

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

instance Pretty a => Pretty (Either String a) where
    ppr _ (Left err) = return (PP.text ("ERROR " ++ err))
    ppr _ (Right a) = ppr 0 a

parr' a b c = PP.hang a (-2) (PP.text "→" <> b <+> c)
parr a b = PP.hang a (-2) (PP.text "→" <+> b)
prettyParen True = PP.parens
prettyParen False = id
pbind b n k e = PP.hang (PP.text b <> PP.parens (PP.text (show n) <+> PP.colon <+> k) <> PP.text ".") 2 e
pbinds p c k b = fmap (prettyParen (p > 0)) . lunbind b $ \(n,t) ->
    pbind c n <$> ppr 0 k <*> ppr 0 t
pbinder p c (TLambda k b) = pbinds p c k b
pbinder p c t = prettyParen (p > 0) <$> ((PP.text c <+>) <$> ppr 1 t)
papp p t1 t2 = prettyParen (p > 1) <$> ((<+>) <$> ppr 1 t1 <*> ppr 2 t2)

-- EXAMPLE SUPPORT CODE

infixl 9 #, &
infixr 1 ~>

(&) = TyApp
lam x t e = Lambda t $ bind (string2Name x) e
tlam x k e = TyLambda k $ bind (string2Name x) e
tylam x k t = TLambda k $ bind (string2Name x) t
var = Var . string2Name
tvar = TVar . string2Name
forall k x e = TForall (tylam k x e)
phi f1 f2 = forall "a" KType (f1 # "a" ~> f2 # "a")

class SynApp a where (#) :: a -> a -> a
instance SynApp Expr where (#) = App
instance SynApp Type where (#) = TApp

class SynArr a where (~>) :: a -> a -> a
instance SynArr Type where (~>) = TArr
instance SynArr Kind where (~>) = KArr Positive -- a "reasonable" default

instance IsString Expr where fromString = var
instance IsString Type where fromString = tvar

-- EXAMPLES

exIdentity = tlam "a" KType
           . lam "x" "a"
           $ var "x"

exFold = tlam "r" KType
       . tlam "f" (KType ~> KType)
       . lam "f" ("f" # "r" ~> "r")
       . lam "xs" (TMu "f")
       $ Fold "f" "xs"

exRoll = tlam "natf" (KType ~> KType)
       . lam "n" (TMu "natf")
       . lam "succ" (forall "n" KType ("n" ~> "natf" # "n"))
       $ Roll "natf" ("succ" & TMu "natf" # "n")

exBlog = tlam "D_i" (KType ~> KType)
       . tlam "D_j" (KType ~> KType)
       . tlam "prod" (KType ~> KType ~> KType)
       . tlam "Ix_i" KType
       . tlam "Ix_j" KType
       . tlam "Int" KType
       . tlam "ListF" ((KType ~> KType) ~> KType ~> KType)
       . lam "fmap" (forall "f" (KType ~> KType) (forall "a" KType (forall "b" KType (("a" ~> "b") ~> ("f" # "a" ~> "f" # "b")))))
       -- . lam "di2list" ("D_i" `phi` TMu "ListF")
       -- . lam "dj2list" ("D_j" `phi` TMu "ListF")
       -- . lam "tabulate_di" ((tylam KType "a" ("Ix_i" ~> "a")) `phi` "D_i")
       -- . lam "index_di" ("D_i" `phi` (tylam "a" KType ("Ix_i" ~> "a")))
       . lam "tabulate_dj" ((tylam "a" KType ("Ix_j" ~> "a")) `phi` "D_j")
       -- . lam "index_dj" ("D_j" `phi` (tylam "a" KType ("Ix_j" ~> "a")))
       . lam "bucket" ("D_i" # "Ix_j" ~> "D_i" `phi` (tylam "a" KType ("D_j" # (TMu "ListF" # "a"))))
       . lam "divide" ("prod" # "Int" # "Int" ~> "Int")
       . lam "plusinc" ("ListF" # (tylam "a" KType $ "prod" # "a" # "a") # "Int" ~> "prod" # "Int" # "Int")
       . lam "pi" ("Ix_j" ~> "D_j" `phi` (tylam "a" KType "a"))
       . lam "zero" "Int"
       . lam "x" ("D_i" # "Int")
       . lam "c" ("D_i" # "Ix_j")
       $ "tabulate_dj" & "Int" # lam "j" "Ix_j" ("divide" # Fold "plusinc" ("pi" # "j" & {- some of the wheels have fallen off -} (TMu "ListF" # "Int") # (("bucket" # "c" & "Int") # "x")))

