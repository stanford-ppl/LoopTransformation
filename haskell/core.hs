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
          | TForall Kind (Bind (Name Type) Type)
          | TApp Type Type
    deriving (Show)

data Expr = Var (Name Expr)
          | Lambda Type (Bind (Name Expr) Expr)
          | App Expr Expr
          | TyLambda Kind (Bind (Name Type) Expr)
          | TyApp Expr Type
    deriving (Show)

-- FRONTEND LANGUAGE

data UExpr = UVar (Name UExpr)
           | ULambda (Bind (Name UExpr) UExpr)
           | UApp UExpr UExpr
    deriving (Show)

-- UNBOUND NONSENSE

$(derive [''Type, ''Expr, ''Kind, ''Polarity, ''UExpr])

instance Alpha Kind
instance Alpha Type
instance Alpha Expr
instance Alpha Polarity
instance Alpha UExpr

instance Subst Expr Expr where
    isvar (Var v) = Just (SubstName v)
    isvar _ = Nothing
instance Subst Type Type where
    isvar (TVar v) = Just (SubstName v)
    isvar _ = Nothing
instance Subst UExpr UExpr where
    isvar (UVar v) = Just (SubstName v)
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
beta (TForall k b) = do
        lunbind b $ \(x, t) -> do
        t' <- beta t
        return (TForall k (bind x t'))
beta (TApp (TForall _ b) t2) = do
        lunbind b $ \(n, t1) -> do
        return $ subst n t2 t1
beta (TApp t1 t2) =
        TApp <$> beta t1 <*> pure t2
    <|> TApp <$> pure t1 <*> beta t2

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
polarityOf m x (TForall k b) = do
    lunbind b $ \(n, t) -> do
    polarityOf (Map.insert n k m) x t
polarityOf m x (TApp t1 t2) = do
    k <- kindOf m t1
    p1 <- polarityOf m x t1
    p2 <- polarityOf m x t2
    case k of
        KArr p _ _ -> return (lub p1 (p * p2))
        _ -> throwError ("polarityOf: ill-kinded type application of " ++ ppshow t1 ++ " and " ++ ppshow t2)

kindOf :: Map (Name Type) Kind -> Type -> M Kind
kindOf m t = do
    k <- kindOf' m t
    return k

kindOf' :: Map (Name Type) Kind -> Type -> M Kind
kindOf' m (TVar n) = maybe (throwError ("kindOf: unbound variable " ++ show n)) return (Map.lookup n m)
kindOf' m (TForall k b) = do
    lunbind b $ \(n, t) -> do
    let m' = Map.insert n k m
    p <- polarityOf m' n t
    KArr p k <$> kindOf m' t
kindOf' m t@(TArr t1 t2) = do
    k1 <- kindOf m t1
    unless (k1 `aeq` KType) $ throwError ("kindOf: ill-kinded left argument of type arrow " ++ ppshow t)
    kindOf m t2
kindOf' m (TApp t1 t2) = do
    k1 <- kindOf m t1
    k2 <- kindOf m t2
    case k1 of
        KArr _ k11 k12 | k11 `aeq` k2 -> return k12
                       | otherwise -> throwError ("kindOf: could not unify " ++ ppshow k11 ++ " and " ++ ppshow k2 ++ " in " ++ ppshow (TApp t1 t2))
        _ -> throwError ("kindOf: attempt to apply to non-arrow kind " ++ ppshow t1 ++ " : " ++ ppshow k1)

{-
-- XXX assuming all type variables are mono
rankOf :: Kind -> M Rank
rankOf (TVar _) = Mono
rankOf (TArr t1 t2) = do
    r1 <- rankOf t1
    rankOf t2
    case r1 of
        Mono-> return Poly
        _ -> throwError (rankOf "Illegal polymorphic type in domain of function")
rankOf (TForall k b) = do
    lunbind b $ \(n, t) -> rankOf t
    Poly
rankOf (TApp t1 t2) = do
-}

kof = runLFreshM . runErrorT . kindOf typeLib
tof = runLFreshM . runErrorT . typeOf typeLib funLib

typeOf :: Map (Name Type) Kind -> Map (Name Expr) Type -> Expr -> M Type
typeOf km m e = do
    t <- typeOf' km m e
    kindOf km t -- sanity
    normalize t

typeOf' :: Map (Name Type) Kind -> Map (Name Expr) Type -> Expr -> M Type
typeOf' _ m (Var n) = maybe (throwError ("typeOf: unbound variable " ++ show n)) return (Map.lookup n m)
typeOf' km m (Lambda t b) = do
    k <- kindOf km t
    -- this is the prenex restriction
    unless (k `aeq` KType) $ throwError "typeOf: lambda type annotation is not *"
    lunbind b $ \(n, e) -> do
    TArr t <$> typeOf km (Map.insert n t m) e
typeOf' km m (TyLambda k b) = do
    lunbind b $ \(n, e) -> do
    t <- typeOf (Map.insert n k km) m e
    return (TForall k (bind n t)) -- note the forall!
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
        TForall k b
            | k `aeq` k' -> do
                lunbind b $ \(n, t') -> return (subst n t t')
            | otherwise -> throwError ("typeOf: could not unify kinds " ++ ppshow k ++ " and " ++ ppshow k')
        _ -> throwError "typeOf: cannot apply to non-universal quantifier"

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
    ppr p (TForall k b) = pbinds p "∀" k b
    ppr p (TApp t1 t2) = papp p t1 t2

instance Pretty Expr where
    ppr _ (Var n) = return (PP.text (show n))
    ppr p (Lambda t b) = pbinds p "λ" t b
    ppr p (App e1 e2) = papp p e1 e2
    ppr p (TyLambda k b) = pbinds p "Λ" k b
    ppr p (TyApp e t) = papp p e t

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
pbinder p c t = prettyParen (p > 0) <$> ((PP.text c <+>) <$> ppr 1 t)
papp p t1 t2 = prettyParen (p > 1) <$> ((<+>) <$> ppr 1 t1 <*> ppr 2 t2)

-- TYPE INFERENCE

{-
erase :: Expr -> M UExpr
erase (Var n) = return (UVar (translate n))
erase (Lambda _ b) = lunbind b $ \(n, e) -> ULambda . bind (translate n) <$> erase e
erase (App e1 e2) = UApp <$> erase e1 <*> erase e2
erase (TyLambda _ b) = lunbind b $ \(_, e) -> erase e
erase (TyApp e _) = erase e

type Context = Map (Name UExpr) Type

constraintsOf gctx = f Map.empty
    where f ctx e = case e of
            UVar n -> undefined

infer :: Context -> UExpr -> M Expr
infer ctx e = undefined
-}

-- EXAMPLE SUPPORT CODE

infixl 9 #, &
infixr 1 ~>

(&) = TyApp
lam x t e = Lambda t $ bind (string2Name x) e
tlam x k e = TyLambda k $ bind (string2Name x) e
forall x k t = TForall k $ bind (string2Name x) t
tylam = forall
phi f1 f2 = forall "a" KType (f1 # "a" ~> f2 # "a")
-- no let polymorphism
elet x v t e  = App (Lambda t (bind (string2Name x) e)) v
tlet x v k t  = TApp (TForall k (bind (string2Name x) t)) v

class SynApp a where (#) :: a -> a -> a
instance SynApp Expr where (#) = App
instance SynApp Type where (#) = TApp

class SynArr a where (~>) :: a -> a -> a
instance SynArr Type where (~>) = TArr
instance SynArr Kind where (~>) = KArr Positive -- a "reasonable" default

instance IsString Expr where fromString = Var . fromString
instance IsString Type where fromString = TVar . fromString
instance IsString (Name Expr) where fromString = string2Name
instance IsString (Name Type) where fromString = string2Name

-- EXAMPLES

(!:) = (,)
infixr 1 !:

typeLib = Map.fromList
    [ "μ"       !: (KType ~> KType) ~> KType
    , "Prod"    !: KType ~> KType ~> KType
    , "Int"     !: KType
    , "NatF"    !: KType ~> KType
    , "D_i"     !: KType ~> KType
    , "D_j"     !: KType ~> KType
    , "Ix_i"    !: KType
    , "Ix_j"    !: KType
    , "ListF"   !: KType ~> KType ~> KType
    ]

funLib = Map.fromList
    [ "fold"    !: forall "r" KType (forall "f" (KType ~> KType) (("f" # "r" ~> "r") ~> "μ" # "f" ~> "r"))
    , "roll"    !: forall "f" (KType ~> KType) ("f" # ("μ" # "f") ~> "μ" # "f")
    , "fmap"    !: forall "f" (KType ~> KType) (forall "a" KType (forall "b" KType (("a" ~> "b") ~> ("f" # "a" ~> "f" # "b"))))
    , "succF"   !: forall "n" KType ("n" ~> "NatF" # "n")
    , "di2list" !: "D_i" `phi` (tylam "a" KType ("μ" # ("ListF" # "a")))
    , "dj2list" !: "D_j" `phi` (tylam "a" KType ("μ" # ("ListF" # "a")))
    , "tabulate_di" !: (tylam "a" KType ("Ix_i" ~> "a")) `phi` "D_i"
    , "index_di"    !: "D_i" `phi` (tylam "a" KType ("Ix_i" ~> "a"))
    , "index_dj"    !: "D_j" `phi` (tylam "a" KType ("Ix_j" ~> "a"))
    , "tabulate_dj" !: (tylam "a" KType ("Ix_j" ~> "a")) `phi` "D_j"
    , "bucket"  !: "D_i" # "Ix_j" ~> "D_i" `phi` (tylam "a" KType ("D_j" # ("μ" # ("ListF" # "a"))))
    , "pi"      !: "Ix_j" ~> "D_j" `phi` (tylam "a" KType "a")
    ]

env = id

exIdentity = tlam "a" KType
           . lam  "x" "a"
           $ "x"

exFold = tlam "r"  KType
       . tlam "f"  (KType ~> KType)
       . lam  "f"  ("f" # "r" ~> "r")
       . lam  "xs" ("μ" # "f")
       $ "fold" & "r" & "f" # "f" # "xs"

exRoll = lam  "n"    ("μ" # "NatF")
       $ "roll" & "NatF" # ("succF" & ("μ" # "NatF") # "n")

exBlog = env
       . lam "x" ("D_i" # "Int")
       . lam "c" ("D_i" # "Ix_j")
       . lam "divide" ("Prod" # "Int" # "Int" ~> "Int")
       . lam "plusinc" ("ListF" # "Int" # ("Prod" # "Int" # "Int") ~> "Prod" # "Int" # "Int")
       $ "tabulate_dj" & "Int" # lam "j" "Ix_j"
             ("divide" #
                ("fold" &
                    ("Prod" # "Int" # "Int") &
                    ("ListF" # "Int") #
                    "plusinc" #
                    ("pi" # "j" & ("μ" # ("ListF" # "Int")) # (("bucket" # "c" & "Int") # "x"))))
