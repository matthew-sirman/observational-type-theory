{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Eval (
  eqReduce,
  cast,
  eval,
  ($$),
  app',
  quote,
  nbe,
  module MonadEvaluator,
) where

import EvalProp
import MonadEvaluator
import Syntax
import Value

import Control.Monad
import Data.Maybe (fromMaybe)

bindM2 :: Monad m => (a -> b -> m r) -> m a -> m b -> m r
bindM2 f a b = join (liftM2 f a b)

bindM3 :: Monad m => (a -> b -> c -> m r) -> m a -> m b -> m c -> m r
bindM3 f a b c = join (liftM3 f a b c)

bindM4 :: Monad m => (a -> b -> c -> d -> m r) -> m a -> m b -> m c -> m d -> m r
bindM4 f a b c d = join (liftM4 f a b c d)

eqReduce :: forall m. MonadEvaluator m => Env -> Val -> VTy -> Val -> m Val
eqReduce env vt va vu = eqReduceType va
  where
    -- Initially driven just by the type
    eqReduceType :: VTy -> m Val
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
    eqReduceAll :: Val -> VTy -> Val -> m Val
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
                e_prop <- valToVProp ve
                va <- cast a' a e_prop va'
                bindM3 (eqReduce env'') (app' b va) (pure (VU Relevant)) (app' b' va')
              forall_x'_b_eq_b' ve = VPi s x' a' <$> makeFnClosure' (b_eq_b' ve)
          VExists (Name "$e") a'_eq_a <$> makeFnClosure' forall_x'_b_eq_b'
    -- Rule Eq-Σ
    eqReduceAll (VSigma x a b) (VU Relevant) (VSigma _ a' b') = do
      a_eq_a' <- eqReduce env a (VU Relevant) a'
      let b_eq_b' ve va = do
            let env'' = env :> (Bound, ve) :> (Bound, va)
            e_prop <- valToVProp ve
            va' <- cast a a' e_prop va
            bindM3 (eqReduce env'') (app' b va) (pure (VU Relevant)) (app' b' va')
          forall_x_b_eq_b' ve = VPi Relevant x a <$> makeFnClosure' (b_eq_b' ve)
      VExists (Name "$e") a_eq_a' <$> makeFnClosure' forall_x_b_eq_b'
    -- Rule Eq-Quotient
    eqReduceAll (VQuotient a x y r _ _ _ _ _ _ _ _ _ _ _ _) (VU Relevant) (VQuotient a' _ _ r' _ _ _ _ _ _ _ _ _ _ _ _) = do
      a_eq_a' <- eqReduce env a (VU Relevant) a'
      let rxy_eq_rx'y' ve vx vy = do
            let env''' = env :> (Bound, ve) :> (Bound, vx) :> (Bound, vy)
            e_prop <- valToVProp ve
            vx' <- cast a a' e_prop vx
            vy' <- cast a a' e_prop vy
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
      -- tm_b <- quote (level env + 2) =<< app' b (VVar (level env))
      let u_eq_u' ve = do
            let env' = env :> (Bound, ve)
            e_prop <- valToVProp ve
            b_prop <- closureToVProp b
            t_prop <- valToVProp t
            t'_prop <- valToVProp t'
            let ap_B_e = PAp (PU Relevant) x b_prop t_prop t'_prop e_prop
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
            e <- valToVProp ve
            bindM3 (eqReduce env') (cast a a' e t) (pure a') (pure t')
          u_eq_u' ve = do
            let env'' = env :> (Bound, ve) :> (Bound, VVar (level env + 1))
            e <- valToVProp ve
            bindM3 (eqReduce env'') (cast a a' e u) (pure a') (pure u')
          t_eq_t'_and_u_eq_u' ve = VAnd <$> t_eq_t' ve <*> u_eq_u' ve
      VExists (Name "$e") a_eq_a' <$> makeFnClosure' t_eq_t'_and_u_eq_u'
    -- Rule Cons-Eq
    eqReduceAll (VCons c t _) (VMu tag f fty x cs (Just a)) (VCons c' t' _)
      | c == c' = do
          case lookup c cs of
            Nothing -> error "BUG: Impossible (constructor not well typed in equality)"
            Just (_, _, bi, _) -> do
              let muF = VMu tag f fty x cs Nothing
              b_muF_a <- app' bi muF a
              eqReduce env t b_muF_a t'
      | otherwise = pure VEmpty
    -- Rule Mu-Eq
    eqReduceAll (VMu tag _ (VPi _ _ aTy _) _ _ (Just a)) (VU Relevant) (VMu tag' _ _ _ _ (Just a'))
      | tag == tag' = eqReduce env a aTy a'
      | otherwise = pure VEmpty
    -- Rule Box-Eq
    eqReduceAll (VBox a) (VU Relevant) (VBox b) =
      eqReduce env a (VU Irrelevant) b
    -- No reduction rule
    eqReduceAll t a u = pure (VEq t a u)

    -- Test if type has reduced to know its head constructor
    hasTypeHead :: VTy -> Bool
    hasTypeHead VNat = True
    hasTypeHead (VPi {}) = True
    hasTypeHead (VU {}) = True
    hasTypeHead (VSigma {}) = True
    hasTypeHead (VQuotient {}) = True
    hasTypeHead (VId {}) = True
    hasTypeHead _ = False

    -- Test if two known head constructors are different
    headNeq :: VTy -> VTy -> Bool
    headNeq VNat VNat = False
    headNeq (VPi {}) (VPi {}) = False
    headNeq (VU {}) (VU {}) = False
    headNeq (VSigma {}) (VSigma {}) = False
    headNeq (VQuotient {}) (VQuotient {}) = False
    headNeq (VId {}) (VId {}) = False
    headNeq t u = hasTypeHead t && hasTypeHead u

cast :: MonadEvaluator m => VTy -> VTy -> VProp -> Val -> m Val
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
        va <- cast a' a (PPropFst e) va'
        a'_prop <- valToVProp va'
        bindM4 cast (app' b va) (app' b' va') (pure (PApp (PPropSnd e) a'_prop)) (f $$ VApp va)
  VLambda x' <$> makeFnClosure' cast_b_b'
cast (VSigma _ a b) (VSigma _ a' b') e (VPair t u) = do
  t' <- cast a a' (PPropFst e) t
  t_prop <- valToVProp t
  u' <- bindM4 cast (app' b t) (app' b' t') (pure (PApp (PPropSnd e) t_prop)) (pure u)
  pure (VPair t' u')
cast a@(VSigma {}) b@(VSigma {}) e p = do
  t <- p $$ VFst
  u <- p $$ VSnd
  cast a b e (VPair t u)
cast (VQuotient a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (VQuotient a' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) e (VQProj t) =
  VQProj <$> cast a a' (PPropFst e) t
-- TODO: This is currently horrible, possibly try to come up with a better system for
-- proof manipulation
cast (VId {}) (VId {}) _ (VIdRefl _) = undefined
-- cast (VId {}) (VId {}) e (VIdRefl _) =
--   pure (VIdPath ((\e -> Trans (Sym (Fst (Snd e))) (Snd (Snd e))) $$$ e))
cast (VId {}) (VId {}) _ (VIdPath _) = undefined
-- cast (VId va _ _) (VId va' _ _) (VProp pEnv e') (VIdPath (VProp _ e)) =
-- let a = quote lvl va
--     a' = quote lvl va'
-- let t'_eq_t = Sym (Fst (Snd e'))
--     t_eq_u = Ap (Lambda (Name "-") (Cast a a' (Fst e') (Var 0))) e
--     u_eq_u' = Snd (Snd e')
--     t'_eq_u' = Trans t'_eq_t (Trans t_eq_u u_eq_u')
-- pure (VIdPath (VProp env t'_eq_u'))
cast (VMu tag f fty x cs (Just a)) (VMu _ _ _ _ _ (Just a')) e (VCons ci t e') = do
  let (_, _, _, ixi) = fromMaybe (error "BUG: Impossible") (lookup ci cs)
      muF = VMu tag f fty x cs Nothing
  ixi_muF_a_t <- app' ixi muF a t
  ixi_prop <- valToVProp ixi_muF_a_t
  a_prop <- valToVProp a
  a'_prop <- valToVProp a'
  pure (VCons ci t (PTrans ixi_prop a_prop a'_prop e' e))
cast (VBox a) (VBox b) e (VBoxProof t) = do
  t' <- cast a b e (VProp t)
  VBoxProof <$> valToVProp t'
cast a b e t = pure (VCast a b e t)

closure :: forall n m. MonadEvaluator m => Env -> Term Ix -> m (Closure n Val)
closure env t = pure (Closure env t)

branch
  :: MonadEvaluator m
  => Env
  -> (Name, Binder, Binder, Term Ix)
  -> m (Name, Binder, Binder, Closure (A 2) Val)
branch env (c, x, e, t) = (c,x,e,) <$> closure env t

evalSort :: MonadEvaluator m => Relevance -> m Relevance
evalSort Relevant = pure Relevant
evalSort Irrelevant = pure Irrelevant
evalSort (SortMeta m) = do
  s <- lookupSortMeta m
  case s of
    Just s -> pure s
    Nothing -> pure (SortMeta m)

eval :: forall m. MonadEvaluator m => Env -> Term Ix -> m Val
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
eval env p@(PropPair {}) = VProp <$> evalProp' env p
eval env p@(PropFst _) = VProp <$> evalProp' env p
eval env p@(PropSnd _) = VProp <$> evalProp' env p
eval env (Exists x a b) = VExists x <$> eval env a <*> closure env b
eval env (Abort a t) = VAbort <$> eval env a <*> evalProp' env t
eval _ Empty = pure VEmpty
eval env p@One = VProp <$> evalProp' env p
eval _ Unit = pure VUnit
eval env (Eq t a u) = bindM3 (eqReduce env) (eval env t) (eval env a) (eval env u)
eval env p@(Refl _) = VProp <$> evalProp' env p
eval env p@(Sym {}) = VProp <$> evalProp' env p
eval env p@(Trans {}) = VProp <$> evalProp' env p
eval env p@(Ap {}) = VProp <$> evalProp' env p
eval env p@(Transp {}) = VProp <$> evalProp' env p
eval env (Cast a b e t) = bindM4 cast (eval env a) (eval env b) (evalProp' env e) (eval env t)
eval env (Pair t u) = VPair <$> eval env t <*> eval env u
eval env (Fst p) = elimM (eval env p) (pure VFst)
eval env (Snd p) = elimM (eval env p) (pure VSnd)
eval env (Sigma x a b) = VSigma x <$> eval env a <*> closure env b
eval env (Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) = do
  a <- eval env a
  r <- closure env r
  rr <- propClosure' env rr
  rs <- propClosure' env rs
  rt <- propClosure' env rt
  pure (VQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)
eval env (QProj t) = VQProj <$> eval env t
eval env (QElim z b x tpi px py pe p u) = do
  u <- eval env u
  b <- closure env b
  tpi <- closure env tpi
  p <- propClosure' env p
  u $$ VQElim z b x tpi px py pe p
eval env (IdRefl t) = VIdRefl <$> eval env t
eval env (IdPath e) = VIdPath <$> evalProp' env e
eval env (J a t x pf b u t' e) = do
  a <- eval env a
  t <- eval env t
  b <- closure env b
  u <- eval env u
  t' <- eval env t'
  e <- eval env e
  e $$ VJ a t x pf b u t'
eval env (Id a t u) = VId <$> eval env a <*> eval env t <*> eval env u
eval env (BoxProof e) = VBoxProof <$> evalProp' env e
eval env (BoxElim t) = do
  t <- eval env t
  t $$ VBoxElim
eval env (Box a) = VBox <$> eval env a
eval env (Cons c t e) = VCons c <$> eval env t <*> evalProp' env e
eval env (Match t x p bs) = do
  t <- eval env t
  p <- closure env p
  bs <- mapM (branch env) bs
  t $$ VMatch x p bs
eval env (FixedPoint i g f p x c t) = do
  i <- eval env i
  c <- closure env c
  t <- closure env t
  pure (VFixedPoint i g f p x c t Nothing [])
eval env (Mu tag f t x cs) = do
  t <- eval env t
  cs <- mapM (\(ci, si, xi, bi, _, ixi) -> (ci,) <$> ((si,xi,,) <$> closure env bi <*> closure env ixi)) cs
  pure (VMu tag f t x cs Nothing)
eval env (Let _ _ t u) = do
  t <- eval env t
  eval (env :> (Defined, t)) u
eval env (Annotation t _) = eval env t
eval env (Meta mv) = do
  val <- lookupMeta mv
  case val of
    Nothing -> pure (VMeta mv env)
    Just solved -> eval env solved

match
  :: MonadEvaluator m
  => Val
  -> Binder
  -> Closure (A 1) Val
  -> [(Name, Binder, Binder, Closure (A 2) Val)]
  -> m Val
match (VCons c u e) _ _ ((c', _, _, t) : _)
  | c == c' = app' t u (VProp e)
match (VRigid x sp) x' p bs = pure (VRigid x (sp :> VMatch x' p bs))
match (VFlex m env sp) x p bs = pure (VFlex m env (sp :> VMatch x p bs))
match t x p (_ : bs) = match t x p bs
match _ _ _ [] = error "BUG: IMPOSSIBLE (non-total or ill-typed match)!"

infixl 8 $$

($$) :: MonadEvaluator m => Val -> VElim -> m Val
-- Eliminators applied to propositions get pushed under the proposition and
-- never compute
(VProp prop) $$ VApp t = do
  t_prop <- valToVProp t
  pure (VProp (PApp prop t_prop))
(VProp prop) $$ (VNElim z a t0 x ih ts) = do
  a <- closureToVProp a
  t0 <- valToVProp t0
  ts <- closureToVProp ts
  pure (VProp (PNElim z a t0 x ih ts prop))
(VProp prop) $$ VFst = pure (VProp (PFst prop))
(VProp prop) $$ VSnd = pure (VProp (PSnd prop))
(VProp prop) $$ (VQElim z b x tpi px py pe p) = do
  b <- closureToVProp b
  tpi <- closureToVProp tpi
  pure (VProp (PQElim z b x tpi px py pe p prop))
(VProp prop) $$ (VJ a t x pf b u v) = do
  a <- valToVProp a
  t <- valToVProp t
  b <- closureToVProp b
  u <- valToVProp u
  v <- valToVProp v
  pure (VProp (PJ a t x pf b u v prop))
(VProp prop) $$ VBoxElim = pure (VProp (PBoxElim prop))
(VProp prop) $$ (VMatch x p bs) = do
  p <- closureToVProp p
  bs <- mapM (\(c, x, e, t) -> (c,x,e,) <$> closureToVProp t) bs
  pure (VProp (PMatch prop x p bs))
(VLambda _ c) $$ (VApp u) = app' c u
-- Only reduce a fixed point [(fix f) ps a => f (fix f) ps a] when
-- [a] is a normal form; i.e. a constructor. This avoids the risk of
-- infinitely looping.
(VFixedPoint muF g f p x c t (Just a) []) $$ (VApp u@(VCons {})) = do
  let fix_f = VFixedPoint muF g f p x c t Nothing []
  app' t muF fix_f a u
(VFixedPoint muF g f p x c t Nothing []) $$ (VApp u) =
  pure (VFixedPoint muF g f p x c t (Just u) [])
(VFixedPoint muF g f p x c t a sp) $$ u =
  pure (VFixedPoint muF g f p x c t a (sp :> u))
(VMu tag f t xs cs Nothing) $$ (VApp a) = pure (VMu tag f t xs cs (Just a))
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
(VBoxProof e) $$ VBoxElim = pure (VProp e)
t $$ (VMatch x p bs) = match t x p bs
(VRigid x sp) $$ u = pure (VRigid x (sp :> u))
(VFlex m env sp) $$ u = pure (VFlex m env (sp :> u))
_ $$ _ = error "BUG: IMPOSSIBLE (ill-typed evaluation)!"

elimM :: MonadEvaluator m => m Val -> m VElim -> m Val
elimM = bindM2 ($$)

app' :: MonadEvaluator m => ClosureApply m n cl Val => Closure n Val -> cl
app' = app eval

quoteSp :: forall m. MonadEvaluator m => Lvl -> Term Ix -> VSpine -> m (Term Ix)
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
  p <- quoteProp (l + 3) =<< appProp p (PVar l) (PVar (l + 1)) (PVar (l + 2))
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
  bs <- mapM quoteBranch bs
  sp <- quoteSp l base sp
  pure (Match sp x p bs)
  where
    quoteBranch :: (Name, Binder, Binder, Closure (A 2) Val) -> m (Name, Binder, Binder, Term Ix)
    quoteBranch (c, x, e, t) = (c,x,e,) <$> (quote (l + 2) =<< app' t (VVar l) (VVar (l + 1)))
quote :: forall m. MonadEvaluator m => Lvl -> Val -> m (Term Ix)
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
quote lvl (VProp t) = quoteProp lvl t
quote _ VUnit = pure Unit
quote lvl (VEq t a u) = Eq <$> quote lvl t <*> quote lvl a <*> quote lvl u
quote lvl (VCast a b e t) = Cast <$> quote lvl a <*> quote lvl b <*> quoteProp lvl e <*> quote lvl t
quote lvl (VPair t u) = Pair <$> quote lvl t <*> quote lvl u
quote lvl (VSigma x a b) =
  Sigma x <$> quote lvl a <*> (quote (lvl + 1) =<< app' b (VVar lvl))
quote lvl (VQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) = do
  a <- quote lvl a
  r <- quote (lvl + 2) =<< app' r (VVar lvl) (VVar (lvl + 1))
  rr <- quoteProp (lvl + 1) =<< appProp rr (PVar lvl)
  rs <- quoteProp (lvl + 3) =<< appProp rs (PVar lvl) (PVar (lvl + 1)) (PVar (lvl + 2))
  rt <- quoteProp (lvl + 5) =<< appProp rt (PVar lvl) (PVar (lvl + 1)) (PVar (lvl + 2)) (PVar (lvl + 3)) (PVar (lvl + 4))
  pure (Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)
quote lvl (VQProj t) = QProj <$> quote lvl t
quote lvl (VIdRefl t) = IdRefl <$> quote lvl t
quote lvl (VIdPath e) = IdPath <$> quoteProp lvl e
quote lvl (VId a t u) = Id <$> quote lvl a <*> quote lvl t <*> quote lvl u
quote lvl (VCons c t e) = Cons c <$> quote lvl t <*> quoteProp lvl e
quote lvl (VFixedPoint i g f p x c t a sp) = do
  i <- quote lvl i
  c <- quote (lvl + 3) =<< app' c (VVar lvl) (VVar (lvl + 1)) (VVar (lvl + 2))
  t <- quote (lvl + 4) =<< app' t (VVar lvl) (VVar (lvl + 1)) (VVar (lvl + 2)) (VVar (lvl + 3))
  let fix_f = FixedPoint i g f p x c t
  a <- mapM (quote lvl) a
  case a of
    Just a -> quoteSp lvl (App fix_f a) sp
    Nothing -> pure fix_f
quote lvl (VMu tag f fty x cs a) = do
  fty <- quote lvl fty
  let vf = VVar lvl
      vx = VVar (lvl + 1)
      quoteCons
        :: (Name, (Relevance, Binder, Closure (A 2) Val, Closure (A 3) Val))
        -> m (Name, Relevance, Binder, Type Ix, Name, Type Ix)
      quoteCons (ci, (si, xi, bi, ixi)) = do
        let vxi = VVar (lvl + 2)
        bi_f_x <- app' bi vf vx
        ixi_f_x_xi <- app' ixi vf vx vxi
        (ci,si,xi,,f,) <$> quote (lvl + 2) bi_f_x <*> quote (lvl + 3) ixi_f_x_xi
  cs <- mapM quoteCons cs
  let muF = Mu tag f fty x cs
  a <- mapM (quote lvl) a
  case a of
    Just a -> pure (App muF a)
    Nothing -> pure muF
quote lvl (VBoxProof e) = BoxProof <$> quoteProp lvl e
quote lvl (VBox a) = Box <$> quote lvl a

nbe :: MonadEvaluator m => Env -> Term Ix -> m (Term Ix)
nbe env t = eval env t >>= quote (level env)