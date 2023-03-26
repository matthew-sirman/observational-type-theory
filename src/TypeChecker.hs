{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module TypeChecker where

import Control.Lens hiding (Context, Empty, Refl, (:>))
import Control.Monad.Except
import Control.Monad.Oops (throw)
import Control.Monad.Reader
import Control.Monad.State

import Data.Fix (Fix (..))
import Data.IntMap qualified as IM
import Data.Variant hiding (throw)
import Error.Diagnose

import Error
import Syntax

newtype Checker e a = Checker {runChecker :: ExceptT e (State MetaContext) a}
  deriving (Functor, Applicative, Monad, MonadState MetaContext, MonadError e)

type Types = [(Binder, (Relevance, VTy Ix))]

data Context = Context
  { env :: Env Ix
  , types :: Types
  , lvl :: Lvl
  }

names :: Context -> [Binder]
names = map fst . types

emptyContext :: Context
emptyContext = Context {env = [], types = [], lvl = 0}

data MetaEntry
  = Unsolved [Binder]
  | Solved [Binder] (Term Ix)

data SortMetaEntry
  = UnsolvedSort
  | SolvedSort Relevance

data MetaContext = MetaContext
  { _metas :: IM.IntMap MetaEntry
  , _fresh :: MetaVar
  , _sortMetas :: IM.IntMap SortMetaEntry
  , _freshSort :: MetaVar
  }

makeLenses ''MetaContext

instance Show MetaContext where
  show mctx =
    "{ "
      ++ showEntries showMeta (IM.assocs (mctx ^. metas))
      ++ " }"
      ++ "\n{ "
      ++ showEntries showSort (IM.assocs (mctx ^. sortMetas))
      ++ " }"
    where
      showMeta :: (Int, MetaEntry) -> String
      showMeta (m, Unsolved _) = "?" ++ show m
      showMeta (m, Solved ns t) =
        "?"
          ++ show m
          ++ " := "
          ++ prettyPrintTerm ns t

      showSort :: (Int, SortMetaEntry) -> String
      showSort (m, UnsolvedSort) = "?" ++ show m
      showSort (m, SolvedSort s) =
        "?"
          ++ show m
          ++ " := "
          ++ show s

      showEntries :: (a -> String) -> [a] -> String
      showEntries _ [] = ""
      showEntries f [e] = f e
      showEntries f (es :> e) = showEntries f es ++ "\n, " ++ f e

emptyMetaContext :: MetaContext
emptyMetaContext = MetaContext {_metas = IM.empty, _fresh = 0, _sortMetas = IM.empty, _freshSort = 0}

freshMeta :: [Binder] -> Checker (Variant e) MetaVar
freshMeta ns = do
  mv@(MetaVar v) <- gets (^. fresh)
  fresh += 1
  modify (metas %~ IM.insert v (Unsolved ns))
  pure mv

freshSortMeta :: Checker (Variant e) MetaVar
freshSortMeta = do
  mv@(MetaVar v) <- gets (^. freshSort)
  freshSort += 1
  modify (sortMetas %~ IM.insert v UnsolvedSort)
  pure mv

addSolution :: MetaVar -> Term Ix -> Checker (Variant e) ()
addSolution (MetaVar v) solution = do
  entry <- gets (IM.lookup v . (^. metas))
  case entry of
    Nothing -> error "BUG: IMPOSSIBLE!"
    -- We only solve metas with definitionally unique solutions, so if we
    -- re-solve the meta, we must have something equivalent to what we already
    -- had, so we do nothing (ideally this will never even happen)
    Just (Solved {}) -> pure ()
    Just (Unsolved ns) -> modify (metas %~ IM.insert v (Solved ns solution))

addSortSolution :: MetaVar -> Relevance -> Checker (Variant e) ()
addSortSolution (MetaVar v) solution = do
  entry <- gets (IM.lookup v . (^. sortMetas))
  case entry of
    Nothing -> error "BUG: IMPOSSIBLE!"
    Just (SolvedSort _) -> pure ()
    Just UnsolvedSort -> modify (sortMetas %~ IM.insert v (SolvedSort solution))

bindM2 :: Monad m => (a -> b -> m r) -> m a -> m b -> m r
bindM2 f a b = join (liftM2 f a b)

bindM3 :: Monad m => (a -> b -> c -> m r) -> m a -> m b -> m c -> m r
bindM3 f a b c = join (liftM3 f a b c)

bindM4 :: Monad m => (a -> b -> c -> d -> m r) -> m a -> m b -> m c -> m d -> m r
bindM4 f a b c d = join (liftM4 f a b c d)

newtype Evaluator a = Evaluator {runEvaluator :: MetaContext -> a}
  deriving (Functor, Applicative, Monad, MonadReader MetaContext)

class Monad m => MonadEvaluator m where
  evaluate :: Evaluator a -> m a

lookupMeta :: MonadEvaluator m => MetaVar -> m (Maybe (Term Ix))
lookupMeta (MetaVar m) = evaluate $ do
  mctx <- ask
  case IM.lookup m (mctx ^. metas) of
    Nothing -> pure Nothing
    Just (Unsolved _) -> pure Nothing
    Just (Solved _ t) -> pure (Just t)

lookupSortMeta :: MonadEvaluator m => MetaVar -> m (Maybe Relevance)
lookupSortMeta (MetaVar m) = evaluate $ do
  mctx <- ask
  case IM.lookup m (mctx ^. sortMetas) of
    Nothing -> pure Nothing
    Just UnsolvedSort -> pure Nothing
    Just (SolvedSort s) -> pure (Just s)

instance MonadEvaluator Evaluator where
  evaluate = id

instance MonadEvaluator (Checker e) where
  evaluate e = gets (runEvaluator e)

instance PushArgument Evaluator where
  push f = do
    ctx <- ask
    pure (\a -> runEvaluator (f a) ctx)

makeFnClosure' :: (MonadEvaluator m, ClosureApply Evaluator n cl v) => cl -> m (Closure n v)
makeFnClosure' c = evaluate (makeFnClosure c)

eqReduce :: forall m. MonadEvaluator m => Env Ix -> Val Ix -> VTy Ix -> Val Ix -> m (Val Ix)
eqReduce env vt va vu = eqReduceType va
  where
    -- Initially driven just by the type
    eqReduceType :: VTy Ix -> m (Val Ix)
    -- Rule Eq-Fun
    eqReduceType (VPi s x a b) = do
      -- Γ ⊢ f ~[Π(x : A). B] g => Π(x : A). f x ~[B] g x
      -- Γ, x : A ⊢ f x ~[B] g x
      let fx_eq_gx vx = bindM3 (eqReduce (env :> (Bound, vx))) (vt $$ VApp vx) (app' b vx) (vu $$ VApp vx)
      VPi s x a <$> makeFnClosure' fx_eq_gx
    -- Rule Eq-Ω
    eqReduceType (VU Irrelevant) =
      let t_to_u = VFun Irrelevant vt vu
          u_to_t = VFun Irrelevant vu vt
       in pure (VAnd t_to_u u_to_t)
    -- Rule Id-Proof-Eq
    eqReduceType (VId {}) = pure VUnit
    -- Rule Box-Proof-Eq
    eqReduceType (VBox _) = pure VUnit
    -- Other cases require matching on [t] and [u]
    eqReduceType va = eqReduceAll vt va vu

    -- Then driven by terms and type
    eqReduceAll :: Val Ix -> VTy Ix -> Val Ix -> m (Val Ix)
    -- Rules Eq-Univ and Eq-Univ-≠
    eqReduceAll vt (VU Relevant) vu
      | headNeq vt vu = pure VEmpty
    eqReduceAll VNat (VU Relevant) VNat = pure VUnit
    eqReduceAll (VU s) (VU Relevant) (VU s')
      | s == s' = pure VUnit
      | otherwise = pure VEmpty
    -- Rule Eq-Π
    eqReduceAll (VPi s _ a b) (VU Relevant) (VPi s' x' a' b')
      | s == s' = do
          a'_eq_a <- eqReduce env a' (VU s) a
          let b_eq_b' ve va' = do
                let env'' = env :> (Bound, ve) :> (Bound, va')
                e <- quoteToProp env'' ve
                va <- cast a' a e va'
                bindM3 (eqReduce env'') (app' b va) (pure (VU Relevant)) (app' b' va')
              forall_x'_b_eq_b' ve = VPi s x' a' <$> makeFnClosure' (b_eq_b' ve)
          VExists (Name "$e") a'_eq_a <$> makeFnClosure' forall_x'_b_eq_b'
    -- Rule Eq-Σ
    eqReduceAll (VSigma x a b) (VU Relevant) (VSigma _ a' b') = do
      a_eq_a' <- eqReduce env a (VU Relevant) a'
      let b_eq_b' ve va = do
            let env'' = env :> (Bound, ve) :> (Bound, va)
            e <- quoteToProp env'' ve
            va' <- cast a a' e va
            bindM3 (eqReduce env'') (app' b va) (pure (VU Relevant)) (app' b' va')
          forall_x_b_eq_b' ve = VPi Relevant x a <$> makeFnClosure' (b_eq_b' ve)
      VExists (Name "$e") a_eq_a' <$> makeFnClosure' forall_x_b_eq_b'
    -- Rule Eq-Quotient
    eqReduceAll (VQuotient a x y r _ _ _ _ _ _ _ _ _ _ _ _) (VU Relevant) (VQuotient a' _ _ r' _ _ _ _ _ _ _ _ _ _ _ _) = do
      a_eq_a' <- eqReduce env a (VU Relevant) a'
      let rxy_eq_rx'y' ve vx vy = do
            let env''' = env :> (Bound, ve) :> (Bound, vx) :> (Bound, vy)
            e <- quoteToProp env''' ve
            vx' <- cast a a' e vx
            vy' <- cast a a' e vy
            bindM3 (eqReduce env''') (app' r vx vy) (pure (VU Irrelevant)) (app' r' vx' vy')
          forall_y_rxy_eq_rx'y' ve vx = VPi Relevant y a <$> makeFnClosure' (rxy_eq_rx'y' ve vx)
          forall_x_y_rxy_eq_rx'y' ve = VPi Relevant x a <$> makeFnClosure' (forall_y_rxy_eq_rx'y' ve)
      VExists (Name "$e") a_eq_a' <$> makeFnClosure' forall_x_y_rxy_eq_rx'y'
    -- Rule Eq-Zero
    eqReduceAll VZero VNat VZero = pure VUnit
    -- Rule Eq-Zero-Succ
    eqReduceAll VZero VNat (VSucc _) = pure VEmpty
    -- Rule Eq-Succ-Zero
    eqReduceAll (VSucc _) VNat VZero = pure VEmpty
    -- Rule Eq-Succ
    eqReduceAll (VSucc m) VNat (VSucc n) = eqReduceAll m VNat n
    -- Rule Eq-Pair
    eqReduceAll p (VSigma x a b) p' = do
      t <- p $$ VFst
      u <- p $$ VSnd
      t' <- p' $$ VFst
      u' <- p' $$ VSnd
      t_eq_t' <- eqReduce env t a t'
      tm_b <- quote (level env + 2) =<< app' b (VVar (level env))
      let u_eq_u' ve = do
            let env' = env :> (Bound, ve)
            e <- quoteToProp env' ve
            tm_t <- quote (level env') t
            tm_t' <- quote (level env') t'
            let ap_B_e = Ap (U Relevant) x tm_b tm_t tm_t' $$$ e
            let cast_b_t_b_t'_u = bindM4 cast (app' b t) (app' b t') (pure ap_B_e) (pure u)
            bindM3 (eqReduce env') cast_b_t_b_t'_u (app' b t') (pure u')
      VExists (Name "$e") t_eq_t' <$> makeFnClosure' u_eq_u'
    -- Rule Quotient-Proj-Eq
    eqReduceAll (VQProj t) (VQuotient _ _ _ r _ _ _ _ _ _ _ _ _ _ _ _) (VQProj u) = app' r t u
    -- Rule Id-Eq
    eqReduceAll (VId a t u) (VU Relevant) (VId a' t' u') = do
      a_eq_a' <- eqReduce env a (VU Relevant) a'
      let t_eq_t' ve = do
            let env' = env :> (Bound, ve)
            e <- quoteToProp env' ve
            bindM3 (eqReduce env') (cast a a' e t) (pure a') (pure t')
          u_eq_u' ve = do
            let env'' = env :> (Bound, ve) :> (Bound, VVar (level env + 1))
            e <- quoteToProp env'' ve
            bindM3 (eqReduce env'') (cast a a' e u) (pure a') (pure u')
          t_eq_t'_and_u_eq_u' ve = VAnd <$> t_eq_t' ve <*> u_eq_u' ve
      VExists (Name "$e") a_eq_a' <$> makeFnClosure' t_eq_t'_and_u_eq_u'
    -- Rule Box-Eq
    eqReduceAll (VBox a) (VU Relevant) (VBox b) =
      eqReduce env a (VU Irrelevant) b
    -- No reduction rule
    eqReduceAll t a u = pure (VEq t a u)

    -- Test if type has reduced to know its head constructor
    hasTypeHead :: VTy Ix -> Bool
    hasTypeHead VNat = True
    hasTypeHead (VPi {}) = True
    hasTypeHead (VU {}) = True
    hasTypeHead (VSigma {}) = True
    hasTypeHead (VQuotient {}) = True
    hasTypeHead (VId {}) = True
    hasTypeHead _ = False

    -- Test if two known head constructors are different
    headNeq :: VTy Ix -> VTy Ix -> Bool
    headNeq VNat VNat = False
    headNeq (VPi {}) (VPi {}) = False
    headNeq (VU {}) (VU {}) = False
    headNeq (VSigma {}) (VSigma {}) = False
    headNeq (VQuotient {}) (VQuotient {}) = False
    headNeq (VId {}) (VId {}) = False
    headNeq t u = hasTypeHead t && hasTypeHead u

cast :: MonadEvaluator m => VTy Ix -> VTy Ix -> VProp Ix -> Val Ix -> m (Val Ix)
-- Rule Cast-Zero
cast VNat VNat _ VZero = pure VZero
-- Rule Cast-Succ
cast VNat VNat e (VSucc n) = VSucc <$> cast VNat VNat e n
-- Rule Cast-Univ
cast (VU s) (VU s') _ a
  | s == s' = pure a
-- Rule Cast-Pi
cast (VPi _ _ a b) (VPi _ x' a' b') e f = do
  let cast_b_b' va' = do
        va <- cast a' a (PropFst $$$ e) va'
        bindM4 cast (app' b va) (app' b' va') (pure (PropSnd $$$ e)) (f $$ VApp va)
  VLambda x' <$> makeFnClosure' cast_b_b'
cast (VSigma _ a b) (VSigma _ a' b') e (VPair t u) = do
  t' <- cast a a' (PropFst $$$ e) t
  u' <- bindM4 cast (app' b t) (app' b' t') (pure (PropSnd $$$ e)) (pure u)
  pure (VPair t' u')
cast a@(VSigma {}) b@(VSigma {}) e p = do
  t <- p $$ VFst
  u <- p $$ VSnd
  cast a b e (VPair t u)
cast (VQuotient a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (VQuotient a' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) e (VQProj t) =
  VQProj <$> cast a a' (PropFst $$$ e) t
-- TODO: This is currently horrible, possibly try to come up with a better system for
-- proof manipulation
cast (VId {}) (VId {}) _ (VIdRefl _) = undefined
-- cast (VId {}) (VId {}) e (VIdRefl _) =
--   pure (VIdPath ((\e -> Trans (Sym (Fst (Snd e))) (Snd (Snd e))) $$$ e))
cast (VId {}) (VId {}) _ (VIdPath (VProp _ _)) = undefined
-- cast (VId va _ _) (VId va' _ _) (VProp pEnv e') (VIdPath (VProp _ e)) =
-- let a = quote lvl va
--     a' = quote lvl va'
-- let t'_eq_t = Sym (Fst (Snd e'))
--     t_eq_u = Ap (Lambda (Name "-") (Cast a a' (Fst e') (Var 0))) e
--     u_eq_u' = Snd (Snd e')
--     t'_eq_u' = Trans t'_eq_t (Trans t_eq_u u_eq_u')
-- pure (VIdPath (VProp env t'_eq_u'))
cast (VBox a) (VBox b) e (VBoxProof t@(VProp env _)) = do
  t' <- cast a b e (VOne t)
  VBoxProof <$> quoteToProp env t'
cast a b e t = pure (VCast a b e t)

quoteToProp :: MonadEvaluator m => Env Ix -> Val Ix -> m (VProp Ix)
quoteToProp env t = VProp env <$> quote (level env) t

prop :: MonadEvaluator m => Env Ix -> Term Ix -> m (VProp Ix)
prop env t = pure (VProp env t)

closure :: MonadEvaluator m => Env Ix -> Term Ix -> m (Closure n Ix)
closure env t = pure (Closure env t)

branch :: MonadEvaluator m => Env Ix -> Branch Ix -> m (VBranch Ix)
branch env (Branch ZeroP t) = VZeroBranch <$> eval env t
branch env (Branch (SuccP x) t) = VSuccBranch x <$> closure env t

evalSort :: MonadEvaluator m => Relevance -> m Relevance
evalSort Relevant = pure Relevant
evalSort Irrelevant = pure Irrelevant
evalSort (SortMeta m) = do
  s <- lookupSortMeta m
  case s of
    Just s -> pure s
    Nothing -> pure (SortMeta m)

eval :: MonadEvaluator m => Env Ix -> Term Ix -> m (Val Ix)
eval env (Var (Ix x)) = pure (snd (env !! x))
eval _ (U s) = VU <$> evalSort s
eval env (Lambda x e) = pure (VLambda x (Closure env e))
eval env (App t u) = elimM (eval env t) (VApp <$> eval env u)
eval env (Pi s x a b) = VPi <$> evalSort s <*> pure x <*> eval env a <*> closure env b
eval _ Zero = pure VZero
eval env (Succ n) = VSucc <$> eval env n
eval env (NElim z a t0 x ih ts n) = do
  n <- eval env n
  let va = Closure env a
  vt0 <- eval env t0
  let vts = Closure env ts
      elim = VNElim z va vt0 x ih vts
  n $$ elim
eval _ Nat = pure VNat
eval env p@(PropPair {}) = VOne <$> prop env p
eval env p@(PropFst _) = VOne <$> prop env p
eval env p@(PropSnd _) = VOne <$> prop env p
eval env (Exists x a b) = VExists x <$> eval env a <*> closure env b
eval env (Abort a t) = VAbort <$> eval env a <*> prop env t
eval _ Empty = pure VEmpty
eval env p@One = VOne <$> prop env p
eval _ Unit = pure VUnit
eval env (Eq t a u) = bindM3 (eqReduce env) (eval env t) (eval env a) (eval env u)
eval env p@(Refl _) = VOne <$> prop env p
eval env p@(Sym {}) = VOne <$> prop env p
eval env p@(Trans {}) = VOne <$> prop env p
eval env p@(Ap {}) = VOne <$> prop env p
eval env p@(Transp {}) = VOne <$> prop env p
eval env (Cast a b e t) = bindM4 cast (eval env a) (eval env b) (prop env e) (eval env t)
eval env p@(CastRefl {}) = VOne <$> prop env p
eval env (Pair t u) = VPair <$> eval env t <*> eval env u
eval env (Fst p) = elimM (eval env p) (pure VFst)
eval env (Snd p) = elimM (eval env p) (pure VSnd)
eval env (Sigma x a b) = VSigma x <$> eval env a <*> closure env b
eval env (Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) = do
  a <- eval env a
  r <- closure env r
  rr <- prop env rr
  rs <- prop env rs
  rt <- prop env rt
  pure (VQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)
eval env (QProj t) = VQProj <$> eval env t
eval env (QElim z b x tpi px py pe p u) = do
  u <- eval env u
  b <- closure env b
  tpi <- closure env tpi
  p <- prop env p
  u $$ VQElim z b x tpi px py pe p
eval env (IdRefl t) = VIdRefl <$> eval env t
eval env (IdPath e) = VIdPath <$> prop env e
eval env (J a t x pf b u t' e) = do
  a <- eval env a
  t <- eval env t
  b <- closure env b
  u <- eval env u
  t' <- eval env t'
  e <- eval env e
  e $$ VJ a t x pf b u t'
eval env (Id a t u) = VId <$> eval env a <*> eval env t <*> eval env u
eval env (BoxProof e) = VBoxProof <$> prop env e
eval env (BoxElim t) = do
  t <- eval env t
  t $$ VBoxElim
eval env (Box a) = VBox <$> eval env a
eval env (Match t x p bs) = do
  t <- eval env t
  p <- closure env p
  bs <- mapM (branch env) bs
  t $$ VMatch x p bs
eval env (Let _ _ t u) = do
  t <- eval env t
  eval (env :> (Defined, t)) u
eval env (Annotation t _) = eval env t
eval env (Meta mv) = do
  val <- lookupMeta mv
  case val of
    Nothing -> pure (VMeta mv env)
    Just solved -> eval env solved

match :: MonadEvaluator m => Val Ix -> Binder -> Closure (A 1) Ix -> [VBranch Ix] -> m (Val Ix)
match VZero _ _ (VZeroBranch t : _) = pure t
match (VSucc n) _ _ (VSuccBranch _ t : _) = app' t n
match (VRigid x sp) x' p bs = pure (VRigid x (sp :> VMatch x' p bs))
match (VFlex m env sp) x p bs = pure (VFlex m env (sp :> VMatch x p bs))
match t x p (_ : bs) = match t x p bs
match _ _ _ [] = error "BUG: IMPOSSIBLE (non-total or ill-typed match)!"

infixl 8 $$

($$) :: MonadEvaluator m => Val Ix -> VElim Ix -> m (Val Ix)
(VLambda _ c) $$ (VApp u) = app' c u
VZero $$ (VNElim _ _ t0 _ _ _) = pure t0
(VSucc n) $$ elim@(VNElim _ _ _ _ _ ts) = app' ts n =<< n $$ elim
(VPair t _) $$ VFst = pure t
(VPair _ u) $$ VSnd = pure u
(VQProj t) $$ (VQElim _ _ _ tpi _ _ _ _) = app' tpi t
(VIdRefl _) $$ (VJ _ _ _ _ _ u _) = pure u
-- TODO: Currently a mess (as with other inductive equality stuff)
(VIdPath _) $$ (VJ {}) = undefined
-- (VIdPath _) $$ (VJ _ t _ _ b u t') = do
--   b_t_idrefl_t <- app' b t (VIdRefl t)
--   b_t'_idpath_e <- app' b t' VIdPath
--   env <- asks evalEnv
--   lvl <- asks evalLvl

--   let tm_t = quote lvl t
--       tm_t' = quote lvl t'
--       eqJ = Transp tm_t (Name "x") Hole (quote (lvl + 2) (app'))
--   cast b_t_idrefl_t b_t'_idpath_e (VProp env eqJ) u
(VBoxProof e) $$ VBoxElim = pure (VOne e)
t $$ (VMatch x p bs) = match t x p bs
(VOne prop@(VProp env _)) $$ t = do
  -- TODO: level here almost certainly wrong
  let prop' = ($$$ prop) <$> evaluate (push (\p -> quoteSp (level env) p [t]))
  VOne <$> prop'
(VRigid x sp) $$ u = pure (VRigid x (sp :> u))
(VFlex m env sp) $$ u = pure (VFlex m env (sp :> u))
_ $$ _ = error "BUG: IMPOSSIBLE (ill-typed evaluation)!"

elimM :: MonadEvaluator m => m (Val Ix) -> m (VElim Ix) -> m (Val Ix)
elimM = bindM2 ($$)

app' :: MonadEvaluator m => ClosureApply m n cl Ix => Closure n Ix -> cl
app' = app eval

quoteBranch :: MonadEvaluator m => Lvl -> VBranch Ix -> m (Branch Ix)
quoteBranch l (VZeroBranch t) = Branch ZeroP <$> quote l t
quoteBranch l (VSuccBranch x t) = Branch (SuccP x) <$> (quote (l + 1) =<< app' t (VVar l))

quoteSp :: forall m. MonadEvaluator m => Lvl -> Term Ix -> VSpine Ix -> m (Term Ix)
quoteSp _ base [] = pure base
quoteSp l base (sp :> VApp u) = App <$> quoteSp l base sp <*> quote l u
quoteSp l base (sp :> VNElim z a t0 x ih ts) =
  NElim z <$> a' <*> quote l t0 <*> pure x <*> pure ih <*> ts' <*> quoteSp l base sp
  where
    a', ts' :: m (Term Ix)
    a' = quote (l + 1) =<< app' a (VVar l)
    ts' = quote (l + 2) =<< app' ts (VVar l) (VVar (l + 1))
quoteSp l base (sp :> VFst) = Fst <$> quoteSp l base sp
quoteSp l base (sp :> VSnd) = Snd <$> quoteSp l base sp
quoteSp l base (sp :> VQElim z b x tpi px py pe p) = do
  b <- quote (l + 1) =<< app' b (VVar l)
  tpi <- quote (l + 1) =<< app' tpi (VVar l)
  p <- quoteProp l p
  QElim z b x tpi px py pe p <$> quoteSp l base sp
quoteSp l base (sp :> VJ a t x pf b u v) = do
  a <- quote l a
  t <- quote l t
  b <- quote (l + 2) =<< app' b (VVar l) (VVar (l + 1))
  u <- quote l u
  v <- quote l v
  J a t x pf b u v <$> quoteSp l base sp
quoteSp l base (sp :> VBoxElim) = BoxElim <$> quoteSp l base sp
quoteSp l base (sp :> VMatch x p bs) = do
  p <- quote (l + 1) =<< app' p (VVar l)
  bs <- mapM (quoteBranch l) bs
  sp <- quoteSp l base sp
  pure (Match sp x p bs)

quoteProp' :: MonadEvaluator m => Lvl -> Lvl -> VProp Ix -> m (Term Ix)
quoteProp' lvl by (VProp env t) = quoteProp (lvl + by) (VProp (liftEnv by env) t)
  where
    liftEnv :: Lvl -> Env Ix -> Env Ix
    liftEnv 0 env = env
    liftEnv by env = liftEnv (by - 1) env :> (Bound, VVar (lvl + by - 1))

quoteProp :: forall m. MonadEvaluator m => Lvl -> VProp Ix -> m (Term Ix)
quoteProp lvl (VProp env t) = q env t
  where
    q :: Env Ix -> Term Ix -> m (Term Ix)
    q env (Var (Ix x)) = quote lvl (snd (env !! x))
    q env (Lambda x t) =
      Lambda x <$> q' 1 env t
    q env (Pi s x a b) =
      Pi s x <$> q env a <*> q' 1 env b
    q env (NElim z a t0 x ih ts n) = do
      a <- q env a
      t0 <- q env t0
      ts <- q' 2 env ts
      n <- q env n
      pure (NElim z a t0 x ih ts n)
    q env (Exists x a b) =
      Exists x <$> q env a <*> q' 1 env b
    q env (Transp t x pf b u v e) = do
      t <- q env t
      b <- q' 2 env b
      u <- q env u
      v <- q env v
      e <- q env e
      pure (Transp t x pf b u v e)
    q env (Sigma x a b) =
      Sigma x <$> q env a <*> q' 1 env b
    q env (Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) = do
      a <- q env a
      r <- q' 2 env r
      rr <- q' 1 env rr
      rs <- q' 3 env rs
      rt <- q' 5 env rt
      pure (Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)
    q env (QElim z b x tpi px py pe p u) = do
      b <- q' 1 env b
      tpi <- q' 1 env tpi
      p <- q' 3 env p
      u <- q env u
      pure (QElim z b x tpi px py pe p u)
    q env (J a t x pf b u v e) = do
      a <- q env a
      t <- q env t
      b <- q' 2 env b
      u <- q env u
      v <- q env v
      e <- q env e
      pure (J a t x pf b u v e)
    q env (Match t x p bs) = do
      t <- q env t
      p <- q' 1 env p
      bs <- mapM (qBranch env) bs
      pure (Match t x p bs)
    q env (Let x a t u) =
      Let x <$> q env a <*> q env t <*> q' 1 env u
    q env (Fix t) = Fix <$> traverse (q env) t

    qBranch :: Env Ix -> Branch Ix -> m (Branch Ix)
    qBranch env (Branch ZeroP t) = Branch ZeroP <$> q env t
    qBranch env (Branch (SuccP x) t) = Branch (SuccP x) <$> q' 1 env t

    q' :: Lvl -> Env Ix -> Term Ix -> m (Term Ix)
    q' by env t = quoteProp' lvl by (VProp env t)

quote :: MonadEvaluator m => Lvl -> Val Ix -> m (Term Ix)
quote lvl (VRigid x sp) = quoteSp lvl (Var (lvl2ix lvl x)) sp
quote lvl (VFlex mv _ sp) = quoteSp lvl (Meta mv) sp
quote _ (VU s) = pure (U s)
quote lvl (VLambda x t) = Lambda x <$> (quote (lvl + 1) =<< app' t (VVar lvl))
quote lvl (VPi s x a b) = Pi s x <$> quote lvl a <*> (quote (lvl + 1) =<< app' b (VVar lvl))
quote _ VZero = pure Zero
quote lvl (VSucc t) = Succ <$> quote lvl t
quote _ VNat = pure Nat
quote lvl (VExists x a b) =
  Exists x <$> quote lvl a <*> (quote (lvl + 1) =<< app' b (VVar lvl))
quote lvl (VAbort a t) = Abort <$> quote lvl a <*> quoteProp lvl t
quote _ VEmpty = pure Empty
quote lvl (VOne t) = quoteProp lvl t
quote _ VUnit = pure Unit
quote lvl (VEq t a u) = Eq <$> quote lvl t <*> quote lvl a <*> quote lvl u
quote lvl (VCast a b e t) = Cast <$> quote lvl a <*> quote lvl b <*> quoteProp lvl e <*> quote lvl t
quote lvl (VPair t u) = Pair <$> quote lvl t <*> quote lvl u
quote lvl (VSigma x a b) =
  Sigma x <$> quote lvl a <*> (quote (lvl + 1) =<< app' b (VVar lvl))
quote lvl (VQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) =
  Quotient
    <$> quote lvl a
    <*> pure x
    <*> pure y
    <*> (quote (lvl + 2) =<< app' r (VVar lvl) (VVar (lvl + 1)))
    <*> pure rx
    <*> quoteProp' lvl 1 rr
    <*> pure sx
    <*> pure sy
    <*> pure sxy
    <*> quoteProp' lvl 3 rs
    <*> pure tx
    <*> pure ty
    <*> pure tz
    <*> pure txy
    <*> pure tyz
    <*> quoteProp' lvl 5 rt
quote lvl (VQProj t) = QProj <$> quote lvl t
quote lvl (VIdRefl t) = IdRefl <$> quote lvl t
quote lvl (VIdPath e) = IdPath <$> quoteProp lvl e
quote lvl (VId a t u) = Id <$> quote lvl a <*> quote lvl t <*> quote lvl u
quote lvl (VBoxProof e) = BoxProof <$> quoteProp lvl e
quote lvl (VBox a) = Box <$> quote lvl a

normalForm :: MonadEvaluator m => Env Ix -> Term Ix -> m (Term Ix)
normalForm env t = eval env t >>= quote (level env)

bind :: Binder -> Relevance -> VTy Ix -> Context -> Context
bind x s tty ctx =
  ctx
    { types = types ctx :> (x, (s, tty))
    , lvl = lvl ctx + 1
    , env = env ctx :> (Bound, VVar (lvl ctx))
    }

bindR, bindP :: Binder -> VTy Ix -> Context -> Context
bindR x = bind x Relevant
bindP x = bind x Irrelevant

define :: Binder -> Val Ix -> Relevance -> VTy Ix -> Context -> Context
define x t s tty ctx =
  ctx
    { types = types ctx :> (x, (s, tty))
    , lvl = lvl ctx + 1
    , env = env ctx :> (Defined, t)
    }

data PartialRenaming = PRen
  { renaming :: IM.IntMap Lvl
  , dom :: Lvl
  , cod :: Lvl
  }

liftRenaming :: Lvl -> PartialRenaming -> PartialRenaming
liftRenaming 0 = id
liftRenaming n = lift . liftRenaming (n - 1)
  where
    lift :: PartialRenaming -> PartialRenaming
    lift (PRen renaming dom cod@(Lvl c)) =
      PRen (IM.insert c dom renaming) (dom + 1) (cod + 1)

-- Γ -> Γ ⊢ σ : Δ -> Δ ⊢ σ' : Γ
invert
  :: e `CouldBe` UnificationError
  => Position
  -> [Binder]
  -> Lvl
  -> Env Ix
  -> Checker (Variant e) PartialRenaming
invert pos names gamma sub = do
  (dom, renaming) <- inv sub
  pure (PRen {renaming = renaming, dom = dom, cod = gamma})
  where
    inv :: e `CouldBe` UnificationError => Env Ix -> Checker (Variant e) (Lvl, IM.IntMap Lvl)
    inv [] = pure (0, IM.empty)
    inv (sub :> (Defined, _)) = do
      (dom, renaming) <- inv sub
      pure (dom + 1, renaming)
    inv (sub :> (Bound, VVar (Lvl x))) = do
      (dom, renaming) <- inv sub
      when (IM.member x renaming) (throw (NonLinearSpineDuplicate (show (names !! x)) pos))
      pure (dom + 1, IM.insert x dom renaming)
    inv (_ :> (Bound, t)) = do
      tm <- quote gamma t
      throw (NonLinearSpineNonVariable (TS (prettyPrintTerm names tm)) pos)

renameProp
  :: forall e
   . e `CouldBe` UnificationError
  => Position
  -> [Binder]
  -> MetaVar
  -> PartialRenaming
  -> VProp Ix
  -> Checker (Variant e) (Term Ix)
renameProp pos ns m sub (VProp env t) = r (level env) ns sub env t
  where
    r :: Lvl -> [Binder] -> PartialRenaming -> Env Ix -> Term Ix -> Checker (Variant e) (Term Ix)
    r _ ns sub env (Var (Ix x)) = rename pos ns m sub (snd (env !! x))
    r l ns sub env (Lambda x t) =
      Lambda x <$> r l (ns :> x) (lift 1 sub) (extend l 1 env) t
    r l ns sub env (Pi s x a b) =
      Pi s x <$> r l ns sub env a <*> r (l + 1) (ns :> x) (lift 1 sub) (extend l 1 env) b
    r l ns sub env (NElim z a t0 x ih ts n) = do
      a <- r l ns sub env a
      t0 <- r l ns sub env t0
      ts <- r (l + 2) (ns :> x :> ih) (lift 2 sub) (extend l 2 env) ts
      n <- r l ns sub env n
      pure (NElim z a t0 x ih ts n)
    r l ns sub env (Exists x a b) =
      Exists x <$> r l ns sub env a <*> r (l + 1) (ns :> x) (lift 1 sub) (extend l 1 env) b
    r l ns sub env (Transp t x pf b u v e) = do
      t <- r l ns sub env t
      b <- r (l + 2) (ns :> x :> pf) (lift 2 sub) (extend l 2 env) b
      u <- r l ns sub env u
      v <- r l ns sub env v
      e <- r l ns sub env e
      pure (Transp t x pf b u v e)
    r l ns sub env (Sigma x a b) =
      Sigma x <$> r l ns sub env a <*> r (l + 1) (ns :> x) (lift 1 sub) (extend l 1 env) b
    r l ns sub env (Quotient a x y r' rx rr sx sy sxy rs tx ty tz txy tyz rt) = do
      a <- r l ns sub env a
      r' <- r (l + 2) (ns :> x :> y) (lift 2 sub) (extend l 2 env) r'
      rr <- r (l + 1) (ns :> rx) (lift 1 sub) (extend l 1 env) rr
      rs <- r (l + 3) (ns :> sx :> sy :> sxy) (lift 3 sub) (extend l 3 env) rs
      rt <- r (l + 5) (ns :> tx :> ty :> tz :> txy :> tyz) (lift 5 sub) (extend l 5 env) rt
      pure (Quotient a x y r' rx rr sx sy sxy rs tx ty tz txy tyz rt)
    r l ns sub env (QElim z b x tpi px py pe p u) = do
      b <- r (l + 1) (ns :> z) (lift 1 sub) (extend l 1 env) b
      tpi <- r (l + 1) (ns :> x) (lift 1 sub) (extend l 1 env) tpi
      p <- r (l + 3) (ns :> px :> py :> pe) (lift 3 sub) (extend l 3 env) p
      u <- r l ns sub env u
      pure (QElim z b x tpi px py pe p u)
    r l ns sub env (J a t x pf b u v e) = do
      a <- r l ns sub env a
      t <- r l ns sub env t
      b <- r (l + 2) (ns :> x :> pf) (lift 2 sub) (extend l 2 env) b
      u <- r l ns sub env u
      v <- r l ns sub env v
      e <- r l ns sub env e
      pure (J a t x pf b u v e)
    r l ns sub env (Match t x p bs) = do
      t <- r l ns sub env t
      p <- r (l + 1) (ns :> x) (lift 1 sub) (extend l 1 env) p
      bs <- mapM (rBranch l ns sub env) bs
      pure (Match t x p bs)
    r l ns sub env (Let x a t u) =
      Let x <$> r l ns sub env a <*> r l ns sub env t <*> r (l + 1) (ns :> x) (lift 1 sub) (extend l 1 env) u
    r l ns sub env (Fix t) = Fix <$> traverse (r l ns sub env) t

    rBranch :: Lvl -> [Binder] -> PartialRenaming -> Env Ix -> Branch Ix -> Checker (Variant e) (Branch Ix)
    rBranch l ns sub env (Branch ZeroP t) = Branch ZeroP <$> r l ns sub env t
    rBranch l ns sub env (Branch (SuccP x) t) =
      Branch (SuccP x) <$> r (l + 1) (ns :> x) (lift 1 sub) (extend l 1 env) t

    lift :: Lvl -> PartialRenaming -> PartialRenaming
    lift = liftRenaming

    extend :: Lvl -> Lvl -> Env Ix -> Env Ix
    extend _ 0 env = env
    extend lvl by env = extend lvl (by - 1) env :> (Bound, VVar (lvl + by - 1))

renameBranch
  :: forall e
   . e `CouldBe` UnificationError
  => Position
  -> [Binder]
  -> MetaVar
  -> PartialRenaming
  -> VBranch Ix
  -> Checker (Variant e) (Branch Ix)
renameBranch pos ns m sub (VZeroBranch t) = Branch ZeroP <$> rename pos ns m sub t
renameBranch pos ns m sub (VSuccBranch x t) =
  Branch (SuccP x) <$> (rename pos ns m (liftRenaming 1 sub) =<< app' t (VVar (cod sub)))

renameSp
  :: forall e
   . e `CouldBe` UnificationError
  => Position
  -> [Binder]
  -> MetaVar
  -> PartialRenaming
  -> Term Ix
  -> VSpine Ix
  -> Checker (Variant e) (Term Ix)
renameSp _ _ _ _ base [] = pure base
renameSp pos ns m sub base (sp :> VApp u) = do
  sp <- renameSp pos ns m sub base sp
  u <- rename pos ns m sub u
  pure (App sp u)
renameSp pos ns m sub base (sp :> VNElim z a t0 x ih ts) = do
  sp <- renameSp pos ns m sub base sp
  a <- rename pos (ns :> z) m (liftRenaming 1 sub) =<< app' a (VVar (cod sub))
  t0 <- rename pos ns m sub t0
  ts <- rename pos (ns :> x :> ih) m (liftRenaming 2 sub) =<< app' ts (VVar (cod sub)) (VVar (cod sub + 1))
  pure (NElim z a t0 x ih ts sp)
renameSp pos ns m sub base (sp :> VFst) = do
  sp <- renameSp pos ns m sub base sp
  pure (Fst sp)
renameSp pos ns m sub base (sp :> VSnd) = do
  sp <- renameSp pos ns m sub base sp
  pure (Snd sp)
renameSp pos ns m sub base (sp :> VQElim z b x tpi px py pe p) = do
  sp <- renameSp pos ns m sub base sp
  b <- rename pos (ns :> z) m (liftRenaming 1 sub) =<< app' b (VVar (cod sub))
  tpi <- rename pos (ns :> x) m (liftRenaming 1 sub) =<< app' tpi (VVar (cod sub))
  p <- renameProp pos ns m sub p
  pure (QElim z b x tpi px py pe p sp)
renameSp pos ns m sub base (sp :> VJ a t x pf b u v) = do
  sp <- renameSp pos ns m sub base sp
  a <- rename pos ns m sub a
  t <- rename pos ns m sub t
  b <- rename pos ns m (liftRenaming 2 sub) =<< app' b (VVar (cod sub)) (VVar (cod sub + 1))
  u <- rename pos ns m sub u
  v <- rename pos ns m sub v
  pure (J a t x pf b u v sp)
renameSp pos ns m sub base (sp :> VBoxElim) = do
  sp <- renameSp pos ns m sub base sp
  pure (BoxElim sp)
renameSp pos ns m sub base (sp :> VMatch x p bs) = do
  sp <- renameSp pos ns m sub base sp
  p <- rename pos ns m (liftRenaming 1 sub) =<< app' p (VVar (cod sub))
  bs <- mapM (renameBranch pos ns m sub) bs
  pure (Match sp x p bs)

rename
  :: forall e
   . e `CouldBe` UnificationError
  => Position
  -> [Binder]
  -> MetaVar
  -> PartialRenaming
  -> Val Ix
  -> Checker (Variant e) (Term Ix)
rename pos ns m sub (VRigid (Lvl x) sp) =
  case IM.lookup x (renaming sub) of
    Nothing -> throw (EscapingVariable (show (ns !! x)) pos)
    Just x' -> renameSp pos ns m sub (Var (lvl2ix (dom sub) x')) sp
rename pos ns m sub (VFlex m' _ sp)
  -- TODO: Need to in fact check DAG ordering, not just single MetaVar occurrence.
  -- e.g. might have α := λx. β, β := α (neither directly violate occurs check, but clearly
  -- unsolvable)
  --
  -- POSSIBILITY: throw occurs check if [m' <= m] (i.e. [m'] was created first,
  -- and as such [m] might depend on it)
  | m == m' = throw (OccursCheck m pos)
  | otherwise = renameSp pos ns m sub (Meta m') sp
rename _ _ _ _ (VU s) = pure (U s)
rename pos ns m sub (VLambda x t) =
  Lambda x <$> (rename pos (ns :> x) m (liftRenaming 1 sub) =<< app' t (VVar (cod sub)))
rename pos ns m sub (VPi s x a b) = do
  a <- rename pos ns m sub a
  b <- rename pos (ns :> x) m (liftRenaming 1 sub) =<< app' b (VVar (cod sub))
  pure (Pi s x a b)
rename _ _ _ _ VZero = pure Zero
rename pos ns m sub (VSucc n) = Succ <$> rename pos ns m sub n
rename _ _ _ _ VNat = pure Nat
rename pos ns m sub (VExists x a b) = do
  a <- rename pos ns m sub a
  b <- rename pos (ns :> x) m (liftRenaming 1 sub) =<< app' b (VVar (cod sub))
  pure (Exists x a b)
rename pos ns m sub (VAbort a t) = do
  a <- rename pos ns m sub a
  t <- renameProp pos ns m sub t
  pure (Abort a t)
rename _ _ _ _ VEmpty = pure Empty
rename pos ns m sub (VOne p) = renameProp pos ns m sub p
rename _ _ _ _ VUnit = pure Unit
rename pos ns m sub (VEq t a u) = do
  t <- rename pos ns m sub t
  a <- rename pos ns m sub a
  u <- rename pos ns m sub u
  -- As the substitution strictly replaces variables with variables,
  -- a blocked [~] will still be blocked, therefore we don't need to
  -- reduce it.
  pure (Eq t a u)
rename pos ns m sub (VCast a b e t) = do
  a <- rename pos ns m sub a
  b <- rename pos ns m sub b
  e <- renameProp pos ns m sub e
  t <- rename pos ns m sub t
  -- As with [~], [cast] must have been blocked, and therefore must still
  -- be blocked.
  pure (Cast a b e t)
rename pos ns m sub (VPair t u) = do
  t <- rename pos ns m sub t
  u <- rename pos ns m sub u
  pure (Pair t u)
rename pos ns m sub (VSigma x a b) = do
  a <- rename pos ns m sub a
  b <- rename pos (ns :> x) m (liftRenaming 1 sub) =<< app' b (VVar (cod sub))
  pure (Sigma x a b)
rename pos ns m sub (VQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) = do
  a <- rename pos ns m sub a
  r <- rename pos (ns :> x :> y) m (liftRenaming 2 sub) =<< app' r (VVar (cod sub)) (VVar (cod sub + 1))
  rr <- renameProp pos ns m sub rr
  rs <- renameProp pos ns m sub rs
  rt <- renameProp pos ns m sub rt
  pure (Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)
rename pos ns m sub (VQProj t) = QProj <$> rename pos ns m sub t
rename pos ns m sub (VIdRefl t) = IdRefl <$> rename pos ns m sub t
rename pos ns m sub (VIdPath e) = IdPath <$> renameProp pos ns m sub e
rename pos ns m sub (VId a t u) = do
  a <- rename pos ns m sub a
  t <- rename pos ns m sub t
  u <- rename pos ns m sub u
  pure (Id a t u)
rename pos ns m sub (VBoxProof e) = BoxProof <$> renameProp pos ns m sub e
rename pos ns m sub (VBox a) = Box <$> rename pos ns m sub a

-- Solve a metavariable, possibly applied to a spine of eliminators
solve
  :: e `CouldBe` UnificationError
  => Position
  -> [Binder]
  -> Lvl
  -> MetaVar
  -> Env Ix
  -> VSpine Ix
  -> Val Ix
  -> Checker (Variant e) ()
solve pos names lvl mv sub [] t = do
  inv <- invert pos names lvl sub
  t' <- rename pos names mv inv t
  addSolution mv t'
solve pos names lvl mv sub (sp :> VApp u@(VVar (Lvl x))) t = do
  -- We start with a judgement of the form
  --  Γ ⊢ α[σ] x ≡ t
  -- So, we create a fresh meta, β, and assign
  --  α := λx. β
  -- Then, we have
  --  Γ ⊢ (λx. β)[σ] x => β[σ, x]
  -- So, we must now solve
  --  Γ ⊢ β[σ, x] ≡ t
  -- In particular, we solve for β in the same context; the level does not change
  body <- freshMeta names
  solve pos names lvl body (sub :> (Bound, u)) sp t
  addSolution mv (Lambda (names !! x) (Meta body))
solve pos names lvl _ _ (_ :> VApp u) _ = do
  tm <- quote lvl u
  throw (NonLinearSpineNonVariable (TS (prettyPrintTerm names tm)) pos)
solve pos _ _ mv _ (_ :> VNElim {}) _ =
  throw (NElimInSpine mv pos)
solve pos names lvl mv sub (sp :> VFst) t = do
  fst <- freshMeta names
  snd <- freshMeta names
  solve pos names lvl fst sub sp t
  addSolution mv (Pair (Meta fst) (Meta snd))
solve pos names lvl mv sub (sp :> VSnd) t = do
  fst <- freshMeta names
  snd <- freshMeta names
  solve pos names lvl snd sub sp t
  addSolution mv (Pair (Meta fst) (Meta snd))
solve pos _ _ mv _ (_ :> VQElim {}) _ = do
  throw (QElimInSpine mv pos)
solve pos _ _ mv _ (_ :> VJ {}) _ =
  throw (JInSpine mv pos)
solve pos names lvl mv sub (sp :> VBoxElim) t = do
  body <- freshMeta names
  solve pos names lvl body sub sp t
  addSolution mv (BoxProof (Meta body))
solve pos _ _ mv _ (_ :> VMatch {}) _ =
  throw (MatchInSpine mv pos)

convSort
  :: e `CouldBe` ConversionError
  => Position
  -> Relevance
  -> Relevance
  -> Checker (Variant e) ()
convSort _ Relevant Relevant = pure ()
convSort _ Irrelevant Irrelevant = pure ()
convSort pos Relevant Irrelevant = throw (ConversionBetweenUniverses pos)
convSort pos Irrelevant Relevant = throw (ConversionBetweenUniverses pos)
-- TODO: occurs check for sort metas (?)
convSort _ (SortMeta m) s = addSortSolution m s
convSort _ s (SortMeta m) = addSortSolution m s

conv
  :: forall e
   . ( e `CouldBe` ConversionError
     , e `CouldBe` UnificationError
     )
  => Position
  -> [Binder]
  -> Lvl
  -> Val Ix
  -> Val Ix
  -> Checker (Variant e) ()
conv pos names = conv' names names
  where
    convSp
      :: [Binder]
      -> [Binder]
      -> Lvl
      -> VSpine Ix
      -> VSpine Ix
      -> Checker (Variant e) ()
    convSp _ _ _ [] [] = pure ()
    convSp ns ns' lvl (sp :> VApp u) (sp' :> VApp u') = do
      convSp ns ns' lvl sp sp'
      conv' ns ns' lvl u u'
    convSp ns ns' lvl (sp :> VNElim z a t0 x ih ts) (sp' :> VNElim z' a' t0' x' ih' ts') = do
      convSp ns ns' lvl sp sp'
      let vz = VVar lvl
      a_z <- app' a vz
      a'_z <- app' a' vz
      conv' (ns :> z) (ns' :> z') (lvl + 1) a_z a'_z
      conv' ns ns' lvl t0 t0'
      let vx = VVar lvl
          vih = VVar (lvl + 1)
      ts_x_ih <- app' ts vx vih
      ts'_x_ih <- app' ts' vx vih
      conv' (ns :> x :> ih) (ns' :> x' :> ih') (lvl + 2) ts_x_ih ts'_x_ih
    convSp ns ns' lvl (sp :> VFst) (sp' :> VFst) = convSp ns ns' lvl sp sp'
    convSp ns ns' lvl (sp :> VSnd) (sp' :> VSnd) = convSp ns ns' lvl sp sp'
    convSp ns ns' lvl (sp :> VQElim z b x tpi _ _ _ _) (sp' :> VQElim z' b' x' tpi' _ _ _ _) = do
      convSp ns ns' lvl sp sp'
      let vz = VVar lvl
      b_z <- app' b vz
      b'_z <- app' b' vz
      let vx = VVar lvl
      tpi_x <- app' tpi vx
      tpi'_x <- app' tpi' vx
      conv' (ns :> z) (ns' :> z') (lvl + 1) b_z b'_z
      conv' (ns :> x) (ns' :> x') (lvl + 1) tpi_x tpi'_x
    convSp ns ns' lvl (sp :> VJ a t x pf b u v) (sp' :> VJ a' t' x' pf' b' u' v') = do
      convSp ns ns' lvl sp sp'
      conv' ns ns' lvl a a'
      conv' ns ns' lvl t t'
      let vx = VVar lvl
          vpf = VVar (lvl + 1)
      b_x_pf <- app' b vx vpf
      b'_x_pf <- app' b' vx vpf
      conv' (ns :> x :> pf) (ns' :> x' :> pf') (lvl + 2) b_x_pf b'_x_pf
      conv' ns ns' lvl u u'
      conv' ns ns' lvl v v'
    convSp ns ns' lvl (sp :> VBoxElim) (sp' :> VBoxElim) = convSp ns ns' lvl sp sp'
    convSp ns ns' lvl (sp :> VMatch x p bs) (sp' :> VMatch x' p' bs') = do
      convSp ns ns' lvl sp sp'
      let vx = VVar lvl
      p_x <- app' p vx
      p'_x <- app' p' vx
      conv' (ns :> x) (ns' :> x') (lvl + 1) p_x p'_x
      zipWithM_ convBranch bs bs'
      where
        convBranch :: VBranch Ix -> VBranch Ix -> Checker (Variant e) ()
        convBranch (VZeroBranch t) (VZeroBranch t') = conv' ns ns' lvl t t'
        convBranch (VSuccBranch x t) (VSuccBranch x' t') = do
          let vx = VVar lvl
          t <- app' t vx
          t' <- app' t' vx
          conv' (ns :> x) (ns' :> x') (lvl + 1) t t'
        convBranch _ _ = undefined
    convSp _ _ _ sp sp' =
      throw (RigidSpineMismatch (TS . showElimHead <$> safeHead sp) (TS . showElimHead <$> safeHead sp') pos)
      where
        safeHead :: [a] -> Maybe a
        safeHead [] = Nothing
        safeHead (hd : _) = Just hd

    -- Conversion checking
    conv'
      :: [Binder] -> [Binder] -> Lvl -> Val Ix -> Val Ix -> Checker (Variant e) ()
    -- Rigid-rigid conversion: heads must be equal and spines convertible
    conv' ns ns' lvl (VRigid x sp) (VRigid x' sp')
      | x == x' = convSp ns ns' lvl sp sp'
    -- Flex conversion: attempt to unify
    conv' ns _ lvl (VFlex m env sp) t = solve pos ns lvl m env sp t
    conv' _ ns lvl t (VFlex m env sp) = solve pos ns lvl m env sp t
    conv' _ _ _ (VU s) (VU s') = convSort pos s s'
    conv' ns ns' lvl (VLambda x t) (VLambda x' t') = do
      let vx = VVar lvl
      t_x <- app' t vx
      t'_x <- app' t' vx
      conv' (ns :> x) (ns' :> x') (lvl + 1) t_x t'_x
    conv' ns ns' lvl (VLambda x t) t' = do
      t_x <- app' t (VVar lvl)
      t'_x <- t' $$ VApp (VVar lvl)
      conv' (ns :> x) (ns' :> x) (lvl + 1) t_x t'_x
    conv' ns ns' lvl t (VLambda x' t') = do
      t_x <- t $$ VApp (VVar lvl)
      t'_x <- app' t' (VVar lvl)
      conv' (ns :> x') (ns' :> x') (lvl + 1) t_x t'_x
    conv' ns ns' lvl (VPi s x a b) (VPi s' x' a' b') = do
      convSort pos s s'
      conv' ns ns' lvl a a'
      let vx = VVar lvl
      b_x <- app' b vx
      b'_x <- app' b' vx
      conv' (ns :> x) (ns' :> x') (lvl + 1) b_x b'_x
    conv' _ _ _ VZero VZero = pure ()
    conv' ns ns' lvl (VSucc n) (VSucc n') = conv' ns ns' lvl n n'
    conv' _ _ _ VNat VNat = pure ()
    conv' ns ns' lvl (VExists x a b) (VExists x' a' b') = do
      conv' ns ns' lvl a a'
      let vx = VVar lvl
      b_x <- app' b vx
      b'_x <- app' b' vx
      conv' (ns :> x) (ns' :> x') (lvl + 1) b_x b'_x
    -- Both terms have the same type (by invariant), so [a ≡ a'], and [t] and [t'] are
    -- both of type [⊥], thus also convertible.
    conv' _ _ _ (VAbort {}) (VAbort {}) = pure ()
    conv' _ _ _ VEmpty VEmpty = pure ()
    -- Proof irrelevant, so always convertible
    conv' _ _ _ (VOne {}) _ = pure ()
    conv' _ _ _ _ (VOne {}) = pure ()
    conv' _ _ _ VUnit VUnit = pure ()
    conv' ns ns' lvl (VEq t a u) (VEq t' a' u') = do
      conv' ns ns' lvl t t'
      conv' ns ns' lvl a a'
      conv' ns ns' lvl u u'
    conv' ns ns' lvl (VCast a b _ t) (VCast a' b' _ t') = do
      conv' ns ns' lvl a a'
      conv' ns ns' lvl b b'
      -- [e ≡ e'] follows from proof irrelevance, given [a ≡ a'] and [b ≡ b']
      conv' ns ns' lvl t t'
    conv' ns ns' lvl (VPair t u) (VPair t' u') = do
      conv' ns ns' lvl t t'
      conv' ns ns' lvl u u'
    conv' ns ns' lvl (VPair t u) p = do
      fst_p <- p $$ VFst
      snd_p <- p $$ VSnd
      conv' ns ns' lvl t fst_p
      conv' ns ns' lvl u snd_p
    conv' ns ns' lvl p (VPair t' u') = do
      fst_p <- p $$ VFst
      snd_p <- p $$ VSnd
      conv' ns ns' lvl fst_p t'
      conv' ns ns' lvl snd_p u'
    conv' ns ns' lvl (VSigma x a b) (VSigma x' a' b') = do
      conv' ns ns' lvl a a'
      let vx = VVar lvl
      b_x <- app' b vx
      b'_x <- app' b' vx
      conv' (ns :> x) (ns' :> x') (lvl + 1) b_x b'_x
    conv' ns ns' lvl (VQuotient a x y r _ _ _ _ _ _ _ _ _ _ _ _) (VQuotient a' x' y' r' _ _ _ _ _ _ _ _ _ _ _ _) = do
      conv' ns ns' lvl a a'
      let vx = VVar lvl
          vy = VVar (lvl + 1)
      r_x_y <- app' r vx vy
      r'_x_y <- app' r' vx vy
      conv' (ns :> x :> y) (ns' :> x' :> y') (lvl + 2) r_x_y r'_x_y
    conv' ns ns' lvl (VQProj t) (VQProj t') = conv' ns ns' lvl t t'
    conv' ns ns' lvl (VIdRefl t) (VIdRefl t') = conv' ns ns' lvl t t'
    conv' _ _ _ (VIdPath _) (VIdPath _) = pure ()
    conv' ns ns' lvl (VId a t u) (VId a' t' u') = do
      conv' ns ns' lvl a a'
      conv' ns ns' lvl t t'
      conv' ns ns' lvl u u'
    conv' _ _ _ (VBoxProof _) (VBoxProof _) = pure ()
    conv' ns ns' lvl (VBox a) (VBox a') = conv' ns ns' lvl a a'
    conv' ns ns' lvl a b = do
      aTS <- TS . prettyPrintTerm ns <$> quote lvl a
      bTS <- TS . prettyPrintTerm ns' <$> quote lvl b
      throw (ConversionFailure aTS bTS pos)

ppVal :: MonadEvaluator m => Context -> Val Ix -> m TermString
ppVal gamma v = TS . prettyPrintTerm (names gamma) <$> quote (lvl gamma) v

ppTerm :: Context -> Term Ix -> TermString
ppTerm gamma = TS . prettyPrintTerm (names gamma)

checkSort :: RelevanceF () -> Checker (Variant e) Relevance
checkSort Relevant = pure Relevant
checkSort Irrelevant = pure Irrelevant
checkSort SortHole = SortMeta <$> freshSortMeta

inferVar
  :: forall e
   . CouldBe e InferenceError
  => Position
  -> Types
  -> Name
  -> Checker (Variant e) (Term Ix, VTy Ix, Relevance)
inferVar pos types name = do
  (i, ty, s) <- find types name
  pure (Var i, ty, s)
  where
    find :: Types -> Name -> Checker (Variant e) (Ix, VTy Ix, Relevance)
    find [] name = throw (VariableOutOfScope name pos)
    find (types :> (Name x, (s, a))) x'
      | x == x' = pure (0, a, s)
      | otherwise = do
          (i, a, s) <- find types x'
          pure (i + 1, a, s)
    find (types :> (Hole, _)) x' = do
      (i, a, s) <- find types x'
      pure (i + 1, a, s)

infer
  :: forall e
   . ( e `CouldBe` InferenceError
     , e `CouldBe` CheckError
     , e `CouldBe` ConversionError
     , e `CouldBe` UnificationError
     )
  => Context
  -> Raw
  -> Checker (Variant e) (Term Ix, VTy Ix, Relevance)
infer gamma (R pos (VarF x)) = inferVar pos (types gamma) x
infer _ (R _ (UF s)) = do
  s <- checkSort s
  pure (U s, VU Relevant, Relevant)
infer gamma (R _ (AppF t@(R fnPos _) u)) = do
  (t, tty, s) <- infer gamma t
  (a, b) <- case tty of
    VPi _ _ a b -> pure (a, b)
    VFlex {} -> do
      -- If the type is a metavariable, then construct a fresh Pi type with metas
      -- for each position, and solve the constraint ?α ≡ Π(x : ?β). ?γ
      -- TODO: add more rules like this
      s <- SortMeta <$> freshSortMeta
      a <- Meta <$> freshMeta (names gamma)
      b <- Meta <$> freshMeta (names gamma)
      va <- eval (env gamma) a
      let vb vx = eval (env gamma :> (Bound, vx)) b
      vb <- makeFnClosure' vb
      conv fnPos (names gamma) (lvl gamma) tty (VPi s Hole va vb)
      pure (va, vb)
    _ -> do
      tTS <- ppVal gamma tty
      throw (ApplicationHead tTS fnPos)
  u <- check gamma u a
  vu <- eval (env gamma) u
  b_u <- app' b vu
  pure (App t u, b_u, s)
infer gamma (R _ (PiF s x a b)) = do
  s <- checkSort s
  a <- check gamma a (VU s)
  va <- eval (env gamma) a
  (b, s') <- checkType (bind x s va gamma) b
  pure (Pi s x a b, VU s', Relevant)
-- In general, constructors must be checked, but the simple case of naturals
-- can be inferred.
infer _ (R _ ZeroF) = pure (Zero, VNat, Relevant)
infer gamma (R _ (SuccF n)) = do
  n <- check gamma n VNat
  pure (Succ n, VNat, Relevant)
infer gamma (R _ (NElimF z a t0 x ih ts n)) = do
  (a, s) <- checkType (bindR z VNat gamma) a
  a0 <- eval (env gamma :> (Bound, VZero)) a
  t0 <- check gamma t0 a0
  let vx = VVar (lvl gamma)
  ax <- eval (env gamma :> (Bound, vx)) a
  aSx <- eval (env gamma :> (Bound, VSucc vx)) a
  ts <- check (gamma & bindR x VNat & bind ih s ax) ts aSx
  -- In general, argument to inductor should be inferred, but can be checked
  -- in simple case of Nat
  n <- check gamma n VNat
  vn <- eval (env gamma) n
  an <- eval (env gamma :> (Bound, vn)) a
  pure (NElim z a t0 x ih ts n, an, s)
infer _ (R _ NatF) = pure (Nat, VU Relevant, Relevant)
infer gamma (R _ (FstF () t@(R pos _))) = do
  (t, tty, _) <- infer gamma t
  case tty of
    VExists _ a _ -> pure (PropFst t, a, Irrelevant)
    VSigma _ a _ -> pure (Fst t, a, Relevant)
    _ -> do
      tTS <- ppVal gamma tty
      throw (FstProjectionHead tTS pos)
infer gamma (R _ (SndF () t@(R pos _))) = do
  (t, tty, _) <- infer gamma t
  case tty of
    VExists _ _ b -> do
      b_fst_t <- app' b (VOne (VProp (env gamma) (PropFst t)))
      pure (PropSnd t, b_fst_t, Irrelevant)
    VSigma _ _ b -> do
      vt <- eval (env gamma) t
      b_fst_t <- app' b =<< (vt $$ VFst)
      pure (Snd t, b_fst_t, Relevant)
    _ -> do
      tTS <- ppVal gamma tty
      throw (SndProjectionHead tTS pos)
infer gamma (R _ (ExistsF x a b)) = do
  a <- check gamma a (VU Irrelevant)
  va <- eval (env gamma) a
  b <- check (bindP x va gamma) b (VU Irrelevant)
  pure (Exists x a b, VU Irrelevant, Relevant)
infer gamma (R _ (AbortF a t)) = do
  (a, s) <- checkType gamma a
  va <- eval (env gamma) a
  t <- check gamma t VEmpty
  pure (Abort a t, va, s)
infer _ (R _ EmptyF) = pure (Empty, VU Irrelevant, Relevant)
infer _ (R _ OneF) = pure (One, VUnit, Irrelevant)
infer _ (R _ UnitF) = pure (Unit, VU Irrelevant, Relevant)
infer gamma (R _ (EqF t a u)) = do
  a <- check gamma a (VU Relevant)
  va <- eval (env gamma) a
  t <- check gamma t va
  u <- check gamma u va
  pure (Eq t a u, VU Irrelevant, Relevant)
infer gamma (R _ (ReflF t@(R pos _))) = do
  (t, a, s) <- infer gamma t
  vt <- eval (env gamma) t
  -- aTS <- ppVal gamma a
  -- when (s == Irrelevant) (throw (ReflIrrelevant aTS pos))
  convSort pos s Relevant
  vt_eq_vt <- eqReduce (env gamma) vt a vt
  pure (Refl t, vt_eq_vt, Irrelevant)
infer gamma (R _ (SymF t@(R pos _) u e)) = do
  (t, a, s) <- infer gamma t
  -- aTS <- ppVal gamma a
  -- when (s == Irrelevant) (throw (SymmetryIrrelevant aTS pos))
  convSort pos s Relevant
  u <- check gamma u a
  vt <- eval (env gamma) t
  vu <- eval (env gamma) u
  vt_eq_vu <- eqReduce (env gamma) vt a vu
  e <- check gamma e vt_eq_vu
  vu_eq_vt <- eqReduce (env gamma) vu a vt
  pure (Sym t u e, vu_eq_vt, Irrelevant)
infer gamma (R _ (TransF t@(R pos _) u v e e')) = do
  (t, a, s) <- infer gamma t
  -- aTS <- ppVal gamma a
  -- when (s == Irrelevant) (throw (TransitivityIrrelevant aTS pos))
  convSort pos s Relevant
  u <- check gamma u a
  v <- check gamma v a
  vt <- eval (env gamma) t
  vu <- eval (env gamma) u
  vv <- eval (env gamma) v
  vt_eq_vu <- eqReduce (env gamma) vt a vu
  e <- check gamma e vt_eq_vu
  vu_eq_vv <- eqReduce (env gamma) vu a vv
  e' <- check gamma e' vu_eq_vv
  vt_eq_vv <- eqReduce (env gamma) vt a vv
  pure (Trans t u v e e', vt_eq_vv, Irrelevant)
infer gamma (R _ (ApF b x t u@(R pos _) v e)) = do
  (u, a, s) <- infer gamma u
  -- aTS <- ppVal gamma a
  -- when (s == Irrelevant) (throw (CongruenceDomainIrrelevant aTS pos))
  convSort pos s Relevant
  v <- check gamma v a
  vu <- eval (env gamma) u
  vv <- eval (env gamma) v
  vu_eq_vv <- eqReduce (env gamma) vu a vv
  e <- check gamma e vu_eq_vv
  b <- check gamma b (VU Relevant)
  vb <- eval (env gamma) b
  t <- check (gamma & bindR x a) t vb
  vt_u <- eval (env gamma :> (Bound, vu)) t
  vt_v <- eval (env gamma :> (Bound, vv)) t
  vt_u_eq_vt_v <- eqReduce (env gamma) vt_u vb vt_v
  pure (Ap b x t u v e, vt_u_eq_vt_v, Irrelevant)
infer gamma (R _ (TranspF t@(R pos _) x pf b u t' e)) = do
  (t, va, s) <- infer gamma t
  -- aTS <- ppVal gamma va
  -- when (s == Irrelevant) (throw (TranspIrrelevant aTS pos))
  convSort pos s Relevant
  t' <- check gamma t' va
  vt <- eval (env gamma) t
  vt' <- eval (env gamma) t'
  let vx = VVar (lvl gamma)
  t_eq_x <- eqReduce (env gamma) vt va vx
  b <- check (gamma & bindR x va & bindP pf t_eq_x) b (VU Irrelevant)
  let refl_t = VOne (VProp (env gamma) (Refl t))
  b_t_refl <- eval (env gamma :> (Bound, vt) :> (Bound, refl_t)) b
  u <- check gamma u b_t_refl
  vt_eq_vt' <- eqReduce (env gamma) vt va vt'
  e <- check gamma e vt_eq_vt'
  b_t'_e <- eval (env gamma :> (Bound, vt') :> (Bound, VOne (VProp (env gamma) e))) b
  pure (Transp t x pf b u t' e, b_t'_e, Irrelevant)
infer gamma (R _ (CastF a@(R aPos _) b@(R bPos _) e t)) = do
  (a, s) <- checkType gamma a
  (b, s') <- checkType gamma b
  va <- eval (env gamma) a
  vb <- eval (env gamma) b
  when (s /= s') (throw (CastBetweenUniverses s aPos s' bPos))
  va_eq_vb <- eqReduce (env gamma) va (VU s) vb
  e <- check gamma e va_eq_vb
  t <- check gamma t va
  pure (Cast a b e t, vb, s)
infer gamma (R _ (CastReflF a t)) = do
  a <- check gamma a (VU Relevant)
  va <- eval (env gamma) a
  t <- check gamma t va
  vt <- eval (env gamma) t
  cast_a_a_t <- cast va va (VProp (env gamma) (Refl a)) vt
  t_eq_cast_a_a_t <- eqReduce (env gamma) vt va cast_a_a_t
  pure (CastRefl a t, t_eq_cast_a_a_t, Irrelevant)
infer gamma (R _ (SigmaF x a b)) = do
  a <- check gamma a (VU Relevant)
  va <- eval (env gamma) a
  b <- check (bindR x va gamma) b (VU Relevant)
  pure (Sigma x a b, VU Relevant, Relevant)
infer gamma (R _ (QuotientF a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)) = do
  a <- check gamma a (VU Relevant)
  va <- eval (env gamma) a
  r <- check (gamma & bindR x va & bindR y va) r (VU Irrelevant)
  let vx = VVar (lvl gamma)
      vy = VVar (lvl gamma + 1)
      vz = VVar (lvl gamma + 2)
  vrxx <- eval (env gamma :> (Bound, vx) :> (Bound, vx)) r
  rr <- check (gamma & bindR x va) rr vrxx
  vrxy <- eval (env gamma :> (Bound, vx) :> (Bound, vy)) r
  vryx <- eval (env gamma :> (Bound, vy) :> (Bound, vx)) r
  rs <- check (gamma & bindR sx va & bindR sy va & bindP sxy vrxy) rs vryx
  vryz <- eval (env gamma :> (Bound, vy) :> (Bound, vz)) r
  vrxz <- eval (env gamma :> (Bound, vx) :> (Bound, vz)) r
  rt <-
    check
      ( gamma
          & bindR tx va
          & bindR ty va
          & bindR tz va
          & bindP txy vrxy
          & bindP tyz vryz
      )
      rt
      vrxz
  pure
    ( Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt
    , VU Relevant
    , Relevant
    )
infer gamma (R pos (QElimF z b x tpi px py pe p u)) = do
  (u, uty, _) <- infer gamma u
  case uty of
    VQuotient a _ _ r _ _ _ _ _ (VProp rs_env rs) _ _ _ _ _ _ -> do
      (b, s) <- checkType (gamma & bindR z uty) b
      let vx = VVar (lvl gamma)
          vy = VVar (lvl gamma + 1)
          ve = VVar (lvl gamma + 2)
      b_pix <- eval (env gamma :> (Bound, VQProj vx)) b
      b_piy <- eval (env gamma :> (Bound, VQProj vy)) b
      tpi <- check (gamma & bindR x a) tpi b_pix
      tpi_x <- eval (env gamma :> (Bound, vx)) tpi
      tpi_y <- eval (env gamma :> (Bound, vy)) tpi

      let ve_inv = VProp (rs_env :> (Bound, vx) :> (Bound, vy) :> (Bound, ve)) rs
      tm_tpi_x <- quote (lvl gamma + 3) tpi_x
      tm_tpi_y <- quote (lvl gamma + 3) tpi_y
      let vz = VVar (lvl gamma)
      tm_b <- quote (lvl gamma + 3) =<< eval (env gamma :> (Bound, vz)) b
      let ap_B_e_inv = Ap (U s) z tm_b tm_tpi_x tm_tpi_y $$$ ve_inv
      cast_b_piy_b_pix <- cast b_piy b_pix ap_B_e_inv tpi_y
      tpi_x_eq_tpi_y <- eqReduce (env gamma) tpi_x b_pix cast_b_piy_b_pix

      r_x_y <- app' r vx vy
      let gamma''' = gamma & bindR px a & bindR py a & bindP pe r_x_y
      p <- check gamma''' p tpi_x_eq_tpi_y
      vu <- eval (env gamma) u
      b_u <- eval (env gamma :> (Bound, vu)) b
      pure (QElim z b x tpi px py pe p u, b_u, s)
    _ -> do
      uTS <- ppVal gamma uty
      throw (QuotientHead uTS pos)
infer gamma (R _ (IdReflF t@(R pos _))) = do
  (t, a, s) <- infer gamma t
  aTS <- ppVal gamma a
  when (s == Irrelevant) (throw (IdReflIrrelevant aTS pos))
  vt <- eval (env gamma) t
  pure (IdRefl t, VId a vt vt, Relevant)
infer gamma (R _ (JF a t x pf b u t' e)) = do
  a <- check gamma a (VU Relevant)
  va <- eval (env gamma) a
  t <- check gamma t va
  vt <- eval (env gamma) t
  let vx = VVar (lvl gamma)
  (b, s) <- checkType (gamma & bindR x va & bindR pf (VId va vt vx)) b
  b_t_idrefl_t <- eval (env gamma :> (Bound, vt) :> (Bound, VIdRefl vt)) b
  u <- check gamma u b_t_idrefl_t
  t' <- check gamma t' va
  vt' <- eval (env gamma) t'
  e <- check gamma e (VId va vt vt')
  ve <- eval (env gamma) e
  b_t'_e <- eval (env gamma :> (Bound, vt') :> (Bound, ve)) b
  pure (J a t x pf b u t' e, b_t'_e, s)
infer gamma (R _ (IdF a t u)) = do
  a <- check gamma a (VU Relevant)
  va <- eval (env gamma) a
  t <- check gamma t va
  u <- check gamma u va
  pure (Id a t u, VU Relevant, Relevant)
infer gamma (R pos (BoxElimF e)) = do
  (e, a, _) <- infer gamma e
  case a of
    VBox a -> pure (BoxElim e, a, Relevant)
    _ -> do
      aTS <- ppVal gamma a
      throw (BoxElimHead aTS pos)
infer gamma (R _ (BoxF a)) = do
  a <- check gamma a (VU Irrelevant)
  pure (Box a, VU Relevant, Relevant)
infer gamma (R _ (MatchF t x p bs)) = do
  (t, a, s) <- infer gamma t
  (p, s') <- checkType (gamma & bind x s a) p
  bs <- mapM (checkBranch gamma a p) bs
  -- TODO: check for coverage - this will actually be easier with
  -- more general patterns (for now, we just throw a runtime error for partial
  -- matches)
  vt <- eval (env gamma) t
  vp_t <- eval (env gamma :> (Bound, vt)) p
  pure (Match t x p bs, vp_t, s')
infer gamma (R _ (LetF x a t u)) = do
  (a, s) <- checkType gamma a
  va <- eval (env gamma) a
  t <- check gamma t va
  vt <- eval (env gamma) t
  (u, uty, s') <- infer (define x vt s va gamma) u
  pure (Let x a t u, uty, s')
infer gamma (R _ (AnnotationF t a)) = do
  (a, s) <- checkType gamma a
  va <- eval (env gamma) a
  t <- check gamma t va
  pure (Annotation t a, va, s)
infer gamma (R _ HoleF) = do
  a <- freshMeta (names gamma)
  va <- eval (env gamma) (Meta a)
  t <- freshMeta (names gamma)
  s <- freshSortMeta
  pure (Meta t, va, SortMeta s)
infer _ (R pos _) = throw (InferenceFailure pos)

checkType
  :: ( e `CouldBe` CheckError
     , e `CouldBe` InferenceError
     , e `CouldBe` ConversionError
     , e `CouldBe` UnificationError
     )
  => Context
  -> Raw
  -> Checker (Variant e) (Term Ix, Relevance)
checkType gamma t@(R pos _) = do
  (t, tty, _) <- infer gamma t
  case tty of
    VU s -> pure (t, s)
    _ -> do
      tTS <- ppVal gamma tty
      throw (CheckType tTS pos)

checkBranch
  :: ( e `CouldBe` CheckError
     , e `CouldBe` InferenceError
     , e `CouldBe` ConversionError
     , e `CouldBe` UnificationError
     )
  => Context
  -> VTy Ix
  -> Term Ix
  -> RawBranch
  -> Checker (Variant e) (Branch Ix)
checkBranch gamma ty p (BranchF ZeroP t@(R pos _)) = do
  conv pos (names gamma) (lvl gamma) ty VNat
  p0 <- eval (env gamma :> (Bound, VZero)) p
  t <- check gamma t p0
  pure (Branch ZeroP t)
checkBranch gamma ty p (BranchF (SuccP x) t@(R pos _)) = do
  conv pos (names gamma) (lvl gamma) ty VNat
  let vx = VVar (lvl gamma)
  pSx <- eval (env gamma :> (Bound, VSucc vx)) p
  t <- check (gamma & bindR x VNat) t pSx
  pure (Branch (SuccP x) t)

check
  :: ( e `CouldBe` CheckError
     , e `CouldBe` InferenceError
     , e `CouldBe` ConversionError
     , e `CouldBe` UnificationError
     )
  => Context
  -> Raw
  -> VTy Ix
  -> Checker (Variant e) (Term Ix)
check gamma (R _ (LambdaF x t)) (VPi s _ a b) = do
  b' <- app' b (VVar (lvl gamma))
  t <- check (bind x s a gamma) t b'
  pure (Lambda x t)
check gamma (R pos (LambdaF {})) tty = do
  tTS <- ppVal gamma tty
  throw (CheckLambda tTS pos)
check gamma (R _ (PropPairF t u)) (VExists _ a b) = do
  t <- check gamma t a
  b_t <- app' b (VOne (VProp (env gamma) t))
  u <- check gamma u b_t
  pure (PropPair t u)
check gamma (R pos (PropPairF {})) tty = do
  tTS <- ppVal gamma tty
  throw (CheckPropPair tTS pos)
check gamma (R _ (PairF t u)) (VSigma _ a b) = do
  t <- check gamma t a
  vt <- eval (env gamma) t
  b_t <- app' b vt
  u <- check gamma u b_t
  pure (Pair t u)
check gamma (R pos (PairF {})) tty = do
  tTS <- ppVal gamma tty
  throw (CheckPair tTS pos)
check gamma (R _ (QProjF t)) (VQuotient a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) =
  -- Inductively, VQuotient contains an equivalent relation; no need to check that
  do
    t <- check gamma t a
    pure (QProj t)
check gamma (R pos (QProjF {})) tty = do
  tTS <- ppVal gamma tty
  throw (CheckQuotientProj tTS pos)
check gamma (R _ (IdPathF e)) (VId a t u) = do
  t_eq_u <- eqReduce (env gamma) t a u
  e <- check gamma e t_eq_u
  pure (IdPath e)
check gamma (R pos (IdPathF {})) tty = do
  tTS <- ppVal gamma tty
  throw (CheckIdPath tTS pos)
check gamma (R _ (BoxProofF e)) (VBox a) = do
  e <- check gamma e a
  pure (BoxProof e)
check gamma (R pos (BoxProofF {})) tty = do
  tTS <- ppVal gamma tty
  throw (CheckBoxProof tTS pos)
check gamma (R _ (LetF x a t u)) uty = do
  (a, s) <- checkType gamma a
  va <- eval (env gamma) a
  t <- check gamma t va
  vt <- eval (env gamma) t
  u <- check (define x vt s va gamma) u uty
  pure (Let x a t u)
check gamma t@(R pos _) tty = do
  (t, tty', _) <- infer gamma t
  conv pos (names gamma) (lvl gamma) tty tty'
  pure t
