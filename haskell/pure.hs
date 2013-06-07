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
           , ViewPatterns
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
import Control.Monad.Logic
import Control.Monad.Trans.Writer
import qualified Text.PrettyPrint as PP
import Text.PrettyPrint (Doc, (<+>), (<>))
import Data.String
-- import Debug.Trace

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
          -- widgets
          | Hole
          | Compose Expr [Expr]
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

{-
-- the "stupid" lfresh instance
instance (Fresh m) => LFresh m where
    lfresh = fresh
    avoid _ m = m
    getAvoids = return Set.empty
-}

-- EVALUATION AND TYPE CHECKING

beta :: (Monad m, Applicative m, LFresh m) => Expr -> MaybeT m Expr
beta (Var _ _) = done
beta (Sort _) = done
beta Hole = done
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
beta (Compose t ts) = do
        x <- lfresh (s2n "x")
        return (Lambda t (bind x (foldr App (Var Skolem x) ts)))

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
                Sort Star -> return (f, ta ~> tb')
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
    -- , rel Star  StarStar    StarStar    -- t -> p : *   (DISABLED quantifiers do not have to be prenex)
    , rel Box   Star        StarStar    -- ∀α. t : **   (quantifiers cause polytypes)
    , rel Box   StarStar    StarStar    -- ∀α. p : **   (nested quantifiers are ok)
    , rel Box   Box         Box         -- * -> * : ☐   (type functions on monotypes are monotypes)
    , rel Box   BoxBox      BoxBox      -- * -> ** : ☐☐ (type functions on polytypes are polytypes)
    ]

typeOf :: Context -> Expr -> M Type
typeOf _ (Sort c) = Sort <$> axiom c
typeOf m (Var Skolem n) = maybe (throwError ("typeOf: unbound variable " ++ show n)) return (Map.lookup n m)
typeOf _ (Var Unification _) = throwError "typeOf: illegal unification variable"
typeOf _ Hole = throwError "typeOf: illegal hole"
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
typeOf m e@(Compose _ _) = do
    e' <- runMaybeT (beta e)
    case e' of
        Just e'' -> typeOf m e''
        Nothing -> throwError "typeOf: beta reduction on compose failed"

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
erase _ Hole = throwError "error: illegal hole"
erase m (Lambda t z) = do
    (n, e) <- unbind z
    k <- upGM $ typeOf m t
    -- need to decide if it has computational content
    case k of
        Sort Star -> Lambda Hole . bind (translate n) <$> erase (Map.insert n t m) e
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
erase m (Compose _ ts) = Compose Hole <$> mapM (erase m) ts
erase _ (Pi _ _) = throwError "erase: pi has no computational content"
erase _ (Sort _) = throwError "erase: constant has no computational content"

erz = runGM . erase library

-- TYPE INFERENCE

{-

What's going on here?

* We provide an *untyped* lambda calculus expressed as Expr with all
  binding annotations erased into holes (and type-lambdas removed).
  Ordinarily, typing this calculus would be straightforward, using vanilla
  Hindley-Milner, and then tacking on quantifiers to deal with unresolved
  type variables.

* However, we have a global context which contains terms which are
  typed in the full language.  Programs may refer to these terms, so
  we need to consider them appropriately in the context of HM
  inference. Since we can assume the type judgements are prenex, all
  we need to do is introduce fresh variables to bind to, and then
  provide the necessary type applications.  This is what 'type2hm' is for.

* Furthermore, our language contains type constructors, so when quantifiers
  are being instantiated, we need to fill them in with unification
  variables for what the kinds are.  We then do a second pass to
  generate constraints for these variables and solve them.

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
-- INVARIANT: all types in global context are beta-normalized and in
-- prenex form.  Also, it's pretty important that 'unbind' gives us
-- GLOBALLY unique names!
type2hm :: Context -> Map (Name Type) (Name Type) -> Type -> GM ([(Name Type, Kind)], Type)
type2hm _ _ e@(Sort _) = return ([], e)
type2hm _ _ Hole = throwError "type2hm: illegal hole"
type2hm m u e@(Var Skolem n) | Just n' <- Map.lookup n u = return ([], Var Unification n')
                             | Map.member n m = return ([], e)
                             | otherwise = throwError "type2hm: unbound skolem variable"
-- HACK: to deal with kinds...
type2hm _ _ e@(Var Unification _) = return ([], e)
type2hm m u e@(Pi ta z) = do
    (x, tb) <- unbind z
    k1 <- upGM $ typeOf m ta
    let m' = Map.insert x ta m
    k2 <- upGM $ typeOf m' tb
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
            return ((t, ta) : f, t')
    case (k1, k2) of
        (Sort s1, Sort s2) -> case (s1, s2) of
            (Star, Star)     -> lateral
            (Star, StarStar) -> lateral
            (Box, Star)      -> promote
            (Box, StarStar)  -> promote
            (Box, Box)       -> lateral
            _ -> throwError ("type2hm: not implemented " ++ ppshow s1 ++ ", " ++ ppshow s2 ++ " for " ++ ppshow e)
        _ -> throwError "type2hm: pi not sorts"
type2hm _ _ (Lambda _ _) = throwError "type2hm: illegal unnormalized lambda present in type"
type2hm _ _ (Compose _ _) = throwError "type2hm: illegal unnormalized compose present in type"
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
-- variables.  (This works for types too!)
constraintsOf :: Context -> Expr -> GM ((Expr, Type), [(Type, Type)])
constraintsOf ctx = runWriterT . f Map.empty
  where f m e@(Var Skolem n) = case Map.lookup n m of
            Just t -> return (e, t)
            Nothing -> case Map.lookup n ctx of
                Just t -> do
                    -- notice that 'm' is irrelevant for HM types; this
                    -- is because we have no dependence on terms
                    (vs, t') <- lift $ type2hm ctx Map.empty t
                    return (foldl (\s n -> App s (Var Unification n)) e (map fst vs), t')
                Nothing -> throwError ("constraintsOf: unbound variable " ++ show n)
        f _ (Var Unification _) = throwError "constraintsOf: illegal unification variable"
        f _ Hole = throwError "constraintsOf: illegal hole"
        f m (App e1 e2) = do
            (e1', t1) <- f m e1
            (e2', t2) <- f m e2
            t <- Var Unification <$> fresh (s2n "t")
            tell [(t1, t2 ~> t)]
            return (App e1' e2', t)
        f m (Lambda pret1 z) = do
            t1 <- if pret1 `aeq` Hole then Var Unification <$> fresh (s2n "t") else return pret1
            (x, e) <- unbind z
            (e', t2) <- f (Map.insert x t1 m) e
            return (Lambda t1 (bind x e'), Pi t1 (bind x t2))
        f m (Compose pret1 es) = do
            t1 <- if pret1 `aeq` Hole then Var Unification <$> fresh (s2n "t") else return pret1
            -- XXX variable naming is pretty terrible
            let go rs (e1:es) t2 = do
                    (e1',t1) <- f m e1
                    t <- Var Unification <$> fresh (s2n "t")
                    tell [(t1, t2 ~> t)]
                    go (e1':rs) es t
                go rs [] t2 = do
                    return (Compose t1 rs, t1 ~> t2)
            go [] (reverse es) t1
            {- lazy man's way
            e' <- upGM . runMaybeT $ beta e
            case e' of
                Just e'' -> f m e''
                Nothing -> throwError "constraintsOf: unable to beta-reduce compose"
            -}
        -- these only apply when types are under question (solving kinds)
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

mUnifier (Var Unification k, t) = Just (k, t)
mUnifier (t, Var Unification k) = Just (k, t)
mUnifier _ = Nothing

mBeta (App (Lambda _ z) e, t) = Just (z, e, t)
mBeta (t, App (Lambda _ z) e) = Just (z, e, t)
mBeta _ = Nothing

mArr (App f a, Pi t z) = Just (f, a, t, z)
mArr (Pi t z, App f a) = Just (f, a, t, z)
mArr _ = Nothing

rmap f x = fmap (\(a,b) -> (a, f b)) x
solve :: [(Type, Type)] -> GM [(Name Type, Type)]
solve eq = f False eq [] []
  where f progress eq xeq s = case eq of
            [] -> case xeq of
                [] -> return s
                _ | progress  -> f False (reverse xeq) [] s
                  | otherwise -> throwError ("Could not unify these equations: " ++ ppshow xeq)
            ((t1, t2):eq') | t1 `aeq` t2 -> f progress eq' xeq s
            ((mUnifier -> Just (k, t)):eq') | not (Set.member k (fv t)) ->
                let ts = subst k t
                    mts = map (\(a,b) -> (ts a, ts b))
                in f True (mts eq') (mts xeq) ((k,t):rmap ts s)
            ((Pi u1 z1, Pi u2 z2):eq') -> do
                Just (_, v1, _, v2) <- unbind2 z1 z2
                f progress ((u1,u2):(v1,v2):eq') xeq s
            ((App u1 v1, App u2 v2):eq') -> f progress ((u1,u2):(v1,v2):eq') xeq s
            ((Lambda t1 z1, Lambda t2 z2):eq') -> do
                Just (_, e1, _, e2) <- unbind2 z1 z2
                f progress ((t1,t2):(e1,e2):eq') xeq s
            ((mArr -> Just (g, a, t1, z)):eq') -> do
                -- very limited unification, just pretend the
                -- constructor is (->) a
                (x, t2) <- unbind z
                y <- fresh "y"
                -- we expect this unification variable to immediately
                -- disappear or immediately unify with another lambda
                k <- Var Unification <$> fresh "k"
                f progress ((g,Lambda k (bind y (Pi t1 (bind x (Var Skolem y))))):(a,t2):eq') xeq s
            -- why do we need to check for beta reducibility? if mArr
            -- worked, it might introduce lambdas
            ((mBeta -> Just (z, e, t)):eq') -> do
                (x, e') <- unbind z
                f progress ((subst x e e', t):eq') xeq s
            (eq:eq') -> f False eq' (eq:xeq) s

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
    x <- Var Unification <$> fresh (s2n "_") -- "don't care result type"
    unifyType ctx e x

unifyType :: Context -> Expr -> Type -> GM (Expr, Type)
unifyType ctx e expect_t = do
    ((e, t), eq) <- constraintsOf ctx e
    subs <- solve ((expect_t, t):eq)
    (e', t', inctx, inty) <- hm2type ctx (substs subs e) (substs subs t)
    (_, eq') <- constraintsOf inctx inty
    subs' <- solve eq'
    return (substs subs' e', substs subs' t')

infer = runGM . inferType library

-- REWRITING

-- assumes "id" and "fmap" in the library

type RewriteM = GM

instance Fresh m => Fresh (LogicT m) where
    fresh = lift . fresh

-- XXX There is one important missing ingredient to this: when we
-- conclude something has functor-nature, we should generate a set of
-- constraints on the environment, saying, "This is only true if these
-- are functors."  The idea is to not build polarity into the kind
-- system, but instead use polarity to automatically discharge proof
-- obligations when functor can be automatically created.  I believe
-- this is precisely type-class style constraint solving, where polarity
-- is modeled as two type-classes (positive and negative), an
-- unspecified polarity is when there is no constraint, and a constant
-- polarity is when there are both.
rewrite :: Context -> Expr -> RewriteM Expr
rewrite _ (Sort _) = throwError "rewrite: unexpected sort"
rewrite _ e@(Var _ _) = return e
rewrite _ Hole = throwError "rewrite: unexpected hole"
rewrite m (App e1 e2) = do
    t <- upGM $ typeOf m e2
    k <- upGM $ typeOf m t
    e1' <- rewrite m e1
    e2' <- case k of
        Sort Star -> rewrite m e2
        Sort StarStar -> rewrite m e2
        _ -> return e2
    return (App e1' e2')
rewrite m (Lambda t z) = do
    (x, e) <- unbind z
    Lambda t . bind x <$> rewrite (Map.insert x t m) e
rewrite _ (Pi _ _) = throwError "rewrite: unexpected pi"
rewrite m (Compose t es) = do
    -- do the magic!
    es' <- mapM (rewrite m) es

    -- XXX there are a lot of missing rules. I've just implemented the
    -- really important one:

    -- commute natural transformations to canonical form (in this case,
    -- all loaded on the right; but you can play around and put them on
    -- the left, etc.)

    -- XXX need to do this repeatedly (atm things will only shift once).
    -- Try not to end up with a bubblesort!

    -- What's the general strategy here?  The idea is that we can check
    -- whether or not something is an fmap/natural transformation by
    -- respectively skolemizing a functor/type and checking if the
    -- erased version of the expression unifies with it.  In a real
    -- rewrite system, these checks are the "predicates" which various
    -- rewrite rules run to figure out if things are kosher or not.
    --
    -- Possible optimization: when a function checks out as an
    -- fmap/natural transformation, expand to include the next unit, and
    -- see if fmap/natural transformation nature is preserved!
    --
    let checkFmap ufmap = do
            f <- fresh (s2n "f")
            a <- fresh (s2n "a")
            b <- fresh (s2n "b")
            let m' = Map.insert f (star ~> star) m
                xf = Var Skolem f
                t = App xf (Var Unification a) ~> App xf (Var Unification b)
            lift . runErrorT $ unifyType m' ufmap t
        checkPhi uphi = do
            f <- fresh (s2n "f")
            g <- fresh (s2n "g")
            a <- fresh (s2n "a")
            let m' = Map.insert a star m
                xa = Var Skolem a
                t = App (Var Unification f) xa ~> App (Var Unification g) xa
            lift . runErrorT $ unifyType m' uphi t
        go rs (efmap:ephi:xs) t = do
            ufmap <- erase m efmap
            uphi <- erase m ephi
            ans1 <- checkFmap ufmap
            ans2 <- checkPhi uphi
            let calcNext e = do
                    x <- fresh (s2n "x")
                    upGM $ typeOf (Map.insert x t m) (App e (Var Skolem x))
                nop = go (efmap:rs) (ephi:xs) =<< calcNext efmap
            -- ok go!
            case (ans1, ans2) of
                (Right _, Right _) -> do
                    target <- upGM $ typeOf m (Compose t [ephi, efmap])
                    -- Reconstituting the types is important, since the
                    -- rewrite can still fail at this point.
                    --
                    -- Consider this case:
                    --
                    --      F : * -> *
                    --      G : * -> *
                    --      phi : F (G a) -> a
                    --      f : Int -> G Int
                    --    ----------------------------
                    --      phi . fmap f : F Int -> Int
                    --
                    -- Here we cannot commute, because phi/fmap disagree what the
                    -- functor is.  This is caught when we type-check the
                    -- result of the rewrite.
                    --
                    -- XXX A nontrivial proof obligation is to show that
                    -- this check is sufficient.  This does not seem
                    -- obviously the case, although all the examples I
                    -- can come up with end up working one way or
                    -- another
                    r <- lift . runErrorT $ unifyType m (Compose Hole [ufmap, uphi]) target
                    case r of
                        Right (Compose _ [efmap', ephi'], _) -> go (ephi':rs) (efmap':xs) =<< calcNext ephi'
                        _ -> nop
                _ -> nop
        go rs xs _ = return (reverse xs ++ rs)
    es'' <- go [] (reverse es') t
    return (Compose t es'')

rr = runGM . rewrite library

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

instance (Pretty a, Pretty b, Pretty c) => Pretty (a, b, c) where
    ppr _ (a, b, c) = do
        pa <- ppr 0 a
        pb <- ppr 0 b
        pc <- ppr 0 c
        return (PP.parens (pa <> PP.comma <+> pb <> PP.comma <+> pc))

instance Pretty Sort where
    ppr _ Box = return (PP.text "☐")
    ppr _ BoxBox = return (PP.text "☐☐")
    ppr _ Star = return (PP.text "★")
    ppr _ StarStar = return (PP.text "★★")

instance Pretty Expr where
    ppr _ (Var Skolem n) = return (PP.text (show n))
    ppr _ (Var Unification n) = return (PP.text "?" <> PP.text (show n))
    ppr _ Hole = return (PP.text "_")
    ppr _ (Sort c) = ppr 0 c
    ppr p (Lambda t z) = pbinds p "λ" t z
    -- not perfect: want to look at the sorts to get a better idea for
    -- how to print it...
    ppr p (Pi t z) = fmap (prettyParen (p > 0)) . lunbind z $ \(x, e) -> do
        if Set.member x (fv e)
            then pbind "Π" x <$> ppr 0 t <*> ppr 0 e
            else parr <$> ppr 1 t <*> ppr 0 e
    ppr p (App e1 e2) = prettyParen (p > 1) <$> ((<+>) <$> ppr 1 e1 <*> ppr 2 e2)
    -- no good way to render the type...
    ppr p (Compose _ ts) = prettyParen (p > 0) . PP.hcat . PP.punctuate (PP.text " ∘ ") <$> mapM (ppr 1) ts

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
a ~> b = Pi a $ bind (s2n "_") b -- hope it doesn't conflict!
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
    , "id"      !: forall "a" star ("a" ~> "a")
    , "succF"   !: forall "n" star ("n" ~> "NatF" # "n")
    , "di2list" !: "D_i" `phi` (lam "a" star ("μ" # ("ListF" # "a")))
    , "dj2list" !: "D_j" `phi` (lam "a" star ("μ" # ("ListF" # "a")))
    , "tabulate_di" !: (lam "a" star ("Ix_i" ~> "a")) `phi` "D_i"
    , "index_di"    !: "D_i" `phi` (lam "a" star ("Ix_i" ~> "a"))
    , "index_dj"    !: "D_j" `phi` (lam "a" star ("Ix_j" ~> "a"))
    , "tabulate_dj" !: (lam "a" star ("Ix_j" ~> "a")) `phi` "D_j"
    , "bucket"  !: "D_i" # "Ix_j" ~> "D_i" `phi` (lam "a" star ("D_j" # ("μ" # ("ListF" # "a"))))
    , "pi"      !: "Ix_j" ~> "D_j" `phi` (lam "a" star "a")
    -- sample data
    , "x"       !: "D_i" # "Int"
    , "c"       !: ("D_i" # "Ix_j")
    , "divide"  !: "Prod" # "Int" # "Int" ~> "Int"
    , "plusinc" !: "ListF" # "Int" # ("Prod" # "Int" # "Int") ~> "Prod" # "Int" # "Int"
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

exBlog = "tabulate_dj" # "Int" # lam "j" "Ix_j"
             ("divide" #
                ("fold" #
                    ("Prod" # "Int" # "Int") #
                    ("ListF" # "Int") #
                    "plusinc" #
                    ("pi" # ("μ" # ("ListF" # "Int")) # "j" # (("bucket" # "Int" # "c") # "x"))))

exBlog' = Compose ("D_i" # "Int")
                  [ "tabulate_dj" # "Int"
                  , "fmap" # (lam "a" star ("Ix_j" ~> "a")) # ("μ" # ("ListF" # "Int")) # "Int" #
                        Compose ("μ" # ("ListF" # "Int"))
                                [ "divide"
                                , "fold" # ("Prod" # "Int" # "Int") # ("ListF" # "Int") # "plusinc"
                                ]
                  , "index_dj" # ("μ" # ("ListF" # "Int"))
                  , "bucket" # "Int" # "c"
                  ] # "x"

exCompose = lam "a" star
          . lam "b" star
          . lam "c" star
          . lam "f" ("a" ~> "b")
          . lam "g" ("b" ~> "c")
          $ Compose "a" ["g", "f"]
