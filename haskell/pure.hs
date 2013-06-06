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
-- import Data.Set (Set)
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

data Sort = Star
          | StarStar
          | Box
          | BoxBox
    deriving (Show, Ord, Eq)

data VarInfo = Skolem | Unification
    deriving (Show)

data Expr = Sort Sort
          | Var VarInfo (Name Expr)
          | App Expr Expr
          | Lambda Expr (Bind (Name Expr) Expr)
          | Pi Expr (Bind (Name Expr) Expr)
    deriving (Show)

-- It's all the same, but it can make some type signatures clearer
type Type = Expr
type Kind = Expr

type Context = Map (Name Expr) Type

-- UNBOUND NONSENSE

$(derive [''Expr, ''Sort, ''VarInfo])
instance Alpha Expr
instance Alpha Sort
instance Alpha VarInfo
instance Subst Expr Sort where
instance Subst Expr VarInfo where
instance Subst Expr Expr where
    isvar (Var _ v) = Just (SubstName v)
    isvar _ = Nothing

-- MONAD PLUMBING

done :: MonadPlus m => m a
done = mzero

type M = ErrorT String (LFreshM)

runM = either error id . runLFreshM . runErrorT

-- EVALUATION AND TYPE CHECKING

beta :: Expr -> MaybeT M Expr
beta (Var _ _) = done
beta (Sort _) = done
beta (Pi t z) = lunbind z $ \(x, e) ->
        Pi <$> beta t <*> pure (bind x e)
    <|> Pi <$> pure t <*> fmap (bind x) (beta e)
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

-- assumes normalized and rank-1
prenexify :: Context -> Type -> M Type
prenexify m e = go m e >>= \(f, e') -> return (f e')
  where go m (Pi ta z) = lunbind z $ \(x, tb) -> do
            k <- typeOf m ta
            (f, tb') <- go (Map.insert x ta m) tb
            case k of
                Sort Star -> return (f, Pi ta (bind x tb'))
                Sort Box -> return (Pi ta . bind x . f, tb')
                _ -> throwError "prenexify: error!"
        go _ e = return (id, e)

axiom :: MonadError String m => Sort -> m Sort
axiom Star = return Box
axiom StarStar = return BoxBox
axiom Box = throwError "axiom: ☐ is not typeable"
axiom BoxBox = throwError "axiom: ☐☐ is not typeable"

normalizingSubst n e e' = normalize (subst n e e')

rel a b c = ((a, b), c)
relations = Map.fromList
    -- let α t : *, p : **, * : ☐, **, ☐☐
    [ rel Star  Star        Star        -- t -> t : *   (functions on monotypes are monotypes)
    -- , rel Star  StarStar    StarStar    -- t -> p : *   (quantifiers do not have to be prenex)
    , rel Box   Star        StarStar    -- ∀α. t : **   (quantifiers cause polytypes)
    , rel Box   StarStar    StarStar    -- ∀α. p : **   (nested quantifiers are ok)
    , rel Box   Box         Box         -- * -> * : ☐   (type functions on monotypes are monotypes)
    , rel Box   BoxBox      BoxBox      -- * -> ** : ☐☐ (type functions on polytypes are polytypes)
    ]

typeOf :: Context -> Expr -> M Type
typeOf _ (Sort c) = Sort <$> axiom c
typeOf m (Var Skolem n) = maybe (throwError ("typeOf: unbound variable " ++ show n)) return (Map.lookup n m)
typeOf _ (Var Unification _) = throwError "typeOf: illegal unification variable"
typeOf m e@(App f a) = do
    tf <- typeOf m f
    ta <- typeOf m a
    case tf of
        Pi ta' z | ta `aeq` ta' -> lunbind z $ \(x, tb) -> normalizingSubst x a tb
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
            Just _ -> return (Pi ta (bind x tb))
        _ -> throwError "typeOf: lambda not sorts"
typeOf m (Pi ta z) = lunbind z $ \(x, tb) -> do
    t1 <- typeOf m ta
    t2 <- typeOf (Map.insert x ta m) tb
    case (t1, t2) of
        (Sort s1, Sort s2) -> case Map.lookup (s1, s2) relations of
            Nothing -> throwError "typeOf: pi relation violation"
            Just s3 -> return (Sort s3)
        _ -> throwError "typeOf: pi not sorts"

tof = runM . typeOf library

-- ERASURE

erase :: Context -> Expr -> GM Expr
erase m e@(Var Skolem n) = do
    case Map.lookup n m of
        Nothing -> throwError "erase: unbound variable"
        Just t -> do
            k <- upGM $ typeOf m t
            case k of
                Sort Star -> return e
                Sort StarStar -> return e
                _ -> throwError ("erase: non-computational variable " ++ ppshow e ++ " was not erased")
erase _ (Var Unification _) = throwError "error: illegal unification variable"
erase m (Lambda t z) = do
    -- need to decide if it has computational content
    (n, e) <- unbind z
    k <- upGM $ typeOf m t
    let u = Var Unification (s2n "dummy") -- fake dummy variable!!!
    case k of
        Sort Star -> Lambda u . bind (translate n) <$> erase (Map.insert n t m) e
        Sort StarStar -> throwError "erase: lambda takes polytype as argument"
        _ -> erase (Map.insert n t m) e
erase m (App e1 e2) = do
    t <- upGM $ typeOf m e2
    k <- upGM $ typeOf m t
    let r = App <$> erase m e1 <*> erase m e2
    case k of
        Sort Star -> r
        Sort StarStar -> r
        _ -> erase m e1
erase _ (Pi _ _) = throwError "erase: pi has no computational content"
erase _ (Sort _) = throwError "erase: constant has no computational content"

erz = runGM . erase library

-- TYPE INFERENCE

{-

What's going on here?

* We have an untyped lambda calculus Expr, where all binding annotations
  are fresh unification variables. Ordinarily, typing this
  calculus would be straightforward. (Vanilla Hindley-Milner, and
  for any unresolved type variables, we just slap quantifiers on the
  front until it's good.  There is the somewhat delicate issue of
  let-polymorphism--we then have to muck around with quantifier
  instantiation--however, we're not including it in our language.)

* However, we have a global context which contains terms which are
  typed in the full language.  Untyped Expr may refer to these terms, so
  we need to consider them appropriately.

* In rank-1 polymorphic calculus, this is still not a big deal;
  all such terms can be converted to prenex form, and then the
  variables introduced freshly as new things to bind to.  This is
  what 'type2hm' is for.

-}

type GM = ErrorT String (FreshM)

runGM = either error id . runFreshM . runErrorT
upGM = either throwError return . runLFreshM . runErrorT

-- Convert a type from the full calculus to form appropriate for
-- Hindley-Milner.  Also provides the necessary type applications
-- for the removed quantifiers.
--
-- We need:
--  - a local context 'm' (lets us do kind-checking)
--  - a unification variable map (tells us when a variable is a
--    unification variable and not a skolem one).  Since each
--    instance needs to be freshened, this has to be a map
--  - note: global context is unnecessary; we can infer if a variable is free if
--    it's not in the unification variable map
--
-- INVARIANT: all types in global context are beta-normalized!  Also,
-- it's pretty important that 'unbind' gives us GLOBALLY unique names!
type2hm :: Context -> Map (Name Type) (Name Type) -> Type -> GM (Expr -> Expr, Type)
type2hm _ _ e@(Sort _) = return (id, e)
type2hm m u e@(Var Skolem n) | Just n' <- Map.lookup n u = return (id, Var Unification n')
                             | Map.member n m = return (id, e)
                             | otherwise = throwError "type2hm: unbound skolem variable"
-- HACK: to deal with kinds...
type2hm _ _ e@(Var Unification _) = return (id, e)
type2hm m u e@(Pi ta z) = do
    (x, tb) <- unbind z
    t1 <- upGM $ typeOf m ta
    let m' = Map.insert x ta m
    t2 <- upGM $ typeOf m' tb
    let -- since arrows do not introduce new type variables, u is unmodified;
        -- in fact, lack of dependence states that any further types
        -- should type-check sans the annotation; we thus omit it and
        -- expect an unbound variable error if there actually was a problem
        lateral = do
            (_, ta') <- type2hm m u ta -- assert that this is identity
            (f, tb') <- type2hm m u tb
            return (f, Pi ta' (bind x tb'))
        -- polymorphism! add to the unification variable set but
        -- erase the constructor
        promote = do
            t <- fresh (s2n "t")
            (f, t') <- type2hm m' (Map.insert x t u) tb
            return (f . flip App (Var Unification t), t')
    case (t1, t2) of
        (Sort s1, Sort s2) -> case (s1, s2) of
            (Star, Star)     -> lateral
            (Star, StarStar) -> lateral
            (Box, Star)      -> promote
            (Box, StarStar)  -> promote
            (Box, Box)       -> lateral
            _ -> throwError ("type2hm: not implemented " ++ ppshow s1 ++ ", " ++ ppshow s2 ++ " for " ++ ppshow e)
        _ -> throwError "type2hm: pi not sorts"
type2hm _ _ (Lambda _ _) = throwError "type2hm: illegal unnormalized lambda present in type"
type2hm m u (App t1 t2) = do
    k1 <- upGM $ typeOf m t1
    s1 <- upGM $ typeOf m k1
    case s1 of
        Sort Box -> return ()
        Sort BoxBox -> return ()
        _ -> throwError "type2hm: illegal kind"
    -- no attempt made at normalization; assumed already normalized, so
    -- must be an atomic App
    (_, t1') <- type2hm m u t1 -- assert this is identity
    (f, t2') <- type2hm m u t2
    return (f, App t1' t2')

-- Converts an untyped lambda calculus term into a typed one, while
-- simultaneously generating a list of constraints over unification
-- variables.  Actually, this works for types too!
--
-- XXX: WHAT ABOUT APPLICATIONS?  Idea from Rank 1 polymorphism paper:
-- DELAY it (carrying around the information) until some other
-- type rule forces the shape to be some form
constraintsOf :: Context -> Expr -> GM ((Expr, Type), [(Type, Type)])
constraintsOf ctx = runWriterT . f Map.empty
  where f m e@(Var Skolem n) = case Map.lookup n m of
            Just t -> return (e, t)
            Nothing -> case Map.lookup n ctx of
                Just t -> do
                    -- notice that 'm' is irrelevant for HM types; this
                    -- is because we have no dependence on terms
                    (wrap, t') <- lift $ type2hm ctx Map.empty t
                    return (wrap e, t')
                Nothing -> throwError ("constraintsOf: unbound variable " ++ show n)
        f _ (Var Unification _) = throwError "constraintsOf: illegal unification variable"
        f m (App e1 e2) = do
            (e1', t1) <- f m e1
            (e2', t2) <- f m e2
            t <- Var Unification <$> fresh (s2n "t")
            x <- fresh (s2n "_")
            tell [(t1, Pi t2 (bind x t))]
            return (App e1' e2', t)
        f m (Lambda _ z) = do
            (x, e) <- unbind z
            -- need to freshen the type; ignore the unification variable!
            t1 <- Var Unification <$> fresh (s2n "t")
            (e', t2) <- f (Map.insert x t1 m) e
            return (Lambda t1 (bind x e'), Pi t1 (bind x t2))
        -- these only apply when types are under question
        f _ e@(Sort c) = do
            throwError "constraintsOf: unexpected sort! (we can do it, but what?!)"
            t <- Sort <$> axiom c
            return (e, t)
        f m (Pi t1 z) = do
            (x, t2) <- unbind z
            (t1', k1) <- f m t1
            (t2', k2) <- f (Map.insert x t1' m) t2
            -- assume that entity under question is not a quantifier,
            -- requires us to unpeel quantifiers first!!!
            tell [(k1, Sort Star)]
            -- lack of quantifiers means it's impossible for a polytype
            -- to be introduced
            tell [(k2, Sort Star)]
            return (Pi t1' (bind x t2'), Sort Star)

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
            ((Pi u1 z1, Pi u2 z2):eq') -> do
                Just (_, v1, _, v2) <- unbind2 z1 z2
                f ((u1,u2):(v1,v2):eq') s
            ((App u1 v1, App u2 v2):eq') -> f ((u1,u2):(v1,v2):eq') s
            ((Lambda t1 z1, Lambda t2 z2):eq') -> do
                Just (_, e1, _, e2) <- unbind2 z1 z2
                f ((t1,t2):(e1,e2):eq') s
            ((x,y):_) -> throwError ("Could not unify '" ++ ppshow x ++ "' and '" ++ ppshow y ++ "'")

-- Converts unification variables into quantifiers, but with
-- unification variables as their kinds.
--
-- Also returns an "inner type" (plus updated context) with the
-- quantifiers removed.
hm2type :: Context -> Expr -> Type -> GM (Expr, Type, Context, Type)
hm2type m e t =
    let vs = Set.difference (fv t) (Map.keysSet m)
        generate [] e t inctx inty = return (e, t, inctx, inty)
        generate (x:xs) e t inctx inty = do
            k <- Var Unification <$> fresh (s2n "k")
            generate xs (Lambda k (bind x (subst x (Var Skolem x) e)))
                        (Pi k (bind x (subst x (Var Skolem x) t)))
                        (Map.insert x k inctx)
                        (subst x (Var Skolem x) inty)
    in generate (Set.elems vs) e t m t

inferType :: Context -> Expr -> GM (Expr, Type)
inferType ctx e = do
    ((e, t), eq) <- constraintsOf ctx e
    subs <- solve eq
    (e', t', inctx, inty) <- hm2type ctx (substs subs e) (substs subs t)
    (_, eq') <- constraintsOf inctx inty
    subs' <- solve eq'
    return (substs subs' e', substs subs' t')

infer = runGM . inferType library

-- PRETTY PRINTING

class Pretty p where
    ppr :: (Applicative m, LFresh m) => Int -> p -> m Doc

pprint = putStrLn . ppshow
ppshow = PP.render . runLFreshM . ppr 0

instance Pretty a => Pretty [a] where
    ppr _ xs = PP.vcat <$> mapM (ppr 0) xs

instance Pretty (Map (Name Expr) Type) where
    ppr _ m = PP.vcat <$> mapM f (Map.toList m)
        where f (n, t) = do
                pn <- ppr 0 n
                pt <- ppr 0 t
                return (pn <+> PP.colon <+> pt)

instance Pretty (Name a) where
    ppr _ n = return (PP.text (show n))

instance (Pretty a, Pretty b) => Pretty (a, b) where
    ppr _ (a, b) = do
        pa <- ppr 0 a
        pb <- ppr 0 b
        return (PP.parens (pa <> PP.comma PP.$$ pb))

instance Pretty Sort where
    ppr _ Box = return (PP.text "☐")
    ppr _ BoxBox = return (PP.text "☐☐")
    ppr _ Star = return (PP.text "★")
    ppr _ StarStar = return (PP.text "★★")

instance Pretty Expr where
    ppr _ (Var Skolem n) = return (PP.text (show n))
    ppr _ (Var Unification n) = return (PP.text "?" <> PP.text (show n))
    ppr _ (Sort c) = ppr 0 c
    ppr p (Lambda t z) = pbinds p "λ" t z
    -- not perfect: want to look at the sorts to get a better idea for
    -- how to print it...
    ppr p (Pi t z) = fmap (prettyParen (p > 0)) . lunbind z $ \(x, e) -> do
        if Set.member x (fv e)
            then pbind "Π" x <$> ppr 0 t <*> ppr 0 e
            else parr <$> ppr 1 t <*> ppr 0 e
    ppr p (App e1 e2) = prettyParen (p > 1) <$> ((<+>) <$> ppr 1 e1 <*> ppr 2 e2)

prettyParen True = PP.parens
prettyParen False = id
parr a c = PP.hang a (-2) (PP.text "→"<+> c)
pbind b n k e = PP.hang (PP.text b <> PP.parens (PP.text (show n) <+> PP.colon <+> k) <> PP.text ".") 2 e
pbinds p c k b = fmap (prettyParen (p > 0)) . lunbind b $ \(n,t) ->
    pbind c n <$> ppr 0 k <*> ppr 0 t

-- EXAMPLE SUPPORT CODE

infixl 9 #
infixr 1 ~>

lam x t e = Lambda t $ bind (string2Name x) e
forall x t e = Pi t $ bind (string2Name x) e
(#) = App
a ~> b = Pi a $ bind (s2n "_") b
star = Sort Star
phi f1 f2 = forall "a" star (f1 # "a" ~> f2 # "a")

instance IsString Expr where fromString = Var Skolem . fromString
instance IsString (Name Expr) where fromString = string2Name

(!:) = (,)
infixr 1 !:

addToContext m (x, t) = do
    t' <- prenexify m =<< normalize t
    return (Map.insert x t' m)

library :: Map (Name Expr) Type
library = runM . foldM addToContext Map.empty $
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
                    ("pi" # ("μ" # ("ListF" # "Int")) # "j" # (("bucket" # "Int" # "c") # "x"))))
