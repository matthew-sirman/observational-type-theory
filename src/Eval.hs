{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Eval (
  embedVal,
  embedVal',
  eqReduce,
  cast,
  eval,
  eval',
  ($$),
  closure,
  functorLift,
  quote,
  nbe,
  valIdentity,
  module MonadEvaluator,
) where

import EvalProp
import MonadEvaluator
import Syntax
import Value

import Control.Monad
import Data.Void (absurd)

bindM2 :: Monad m => (a -> b -> m r) -> m a -> m b -> m r
bindM2 f a b = join (liftM2 f a b)

bindM3 :: Monad m => (a -> b -> c -> m r) -> m a -> m b -> m c -> m r
bindM3 f a b c = join (liftM3 f a b c)

bindM4 :: Monad m => (a -> b -> c -> d -> m r) -> m a -> m b -> m c -> m d -> m r
bindM4 f a b c d = join (liftM4 f a b c d)

embedVal :: MonadEvaluator m => Val -> m EnvEntry
embedVal v = fst <$> embedVal' v

embedVal' :: MonadEvaluator m => Val -> m (EnvEntry, Val)
embedVal' v = do
  v_prop <- freeze v
  pure (Val v v_prop, v)

eval' :: MonadEvaluator m => Sort -> Env -> Term Ix -> m EnvEntry
eval' Relevant env t = embedVal =<< eval env t
eval' Irrelevant env t = Prop <$> evalProp env t
eval' (SortMeta m) _ _ = absurd m

instance MonadEvaluator m => ClosureEval m Val where
  closureEval = eval

  closureDefunEval (ClosureEqFun Relevant f b g) v =
    bindM3 eqReduce (f $$ VApp (val v)) (app b v) (g $$ VApp (val v))
  closureDefunEval (ClosureEqFun Irrelevant f b g) v =
    bindM3 eqReduce (f $$ VAppProp (prop v)) (app b v) (g $$ VAppProp (prop v))
  closureDefunEval (ClosureEqFun (SortMeta s) _ _ _) _ = absurd s
  closureDefunEval (ClosureEqPiFamily s ve a a' b b') va' = do
    va <- case s of
      Relevant -> cast a' a (prop ve) (val va') >>= embedVal
      Irrelevant -> do
        a_prop <- freeze a
        a'_prop <- freeze a'
        pure (Prop (PCast a_prop a'_prop (prop ve) (prop va')))
      SortMeta s -> absurd s
    bindM3 eqReduce (app b va) (pure (VU Relevant)) (app b' va')
  closureDefunEval (ClosureEqPi s x a a' b b') ve =
    pure (VPi (fmap absurd s) x a' (Defun (ClosureEqPiFamily s ve a a' b b')))
  closureDefunEval (ClosureEqSigmaFamily ve a a' b b') va = do
    va'_val <- cast a a' (prop ve) (val va)
    va' <- embedVal va'_val
    bindM3 eqReduce (app b va) (pure (VU Relevant)) (app b' va')
  closureDefunEval (ClosureEqSigma x a a' b b') ve =
    pure (VPi Relevant x a (Defun (ClosureEqSigmaFamily ve a a' b b')))
  closureDefunEval (ClosureEqQuotientY ve vx a a' r r') vy = do
    vx'_val <- cast a a' (prop ve) (val vx)
    vx' <- embedVal vx'_val
    vy'_val <- cast a a' (prop ve) (val vy)
    vy' <- embedVal vy'_val
    bindM3 eqReduce (app r vx vy) (pure (VU Irrelevant)) (app r' vx' vy')
  closureDefunEval (ClosureEqQuotientX ve y a a' r r') vx =
    pure (VPi Relevant y a (Defun (ClosureEqQuotientY ve vx a a' r r')))
  closureDefunEval (ClosureEqQuotient x y a a' r r') ve =
    pure (VPi Relevant x a (Defun (ClosureEqQuotientX ve y a a' r r')))
  closureDefunEval (ClosureEqPair x b t t' u u') ve = do
    b_prop <- closureToVProp b
    b_t <- app b t
    b_t' <- app b t'
    let ap_B_e = PAp (PU Relevant) x b_prop (prop t) (prop t') (prop ve)
    cast_b_t_b_t'_u <- cast b_t b_t' ap_B_e u
    eqReduce cast_b_t_b_t'_u b_t' u'
  closureDefunEval (ClosureCastPi s a a' b b' e f) va' = do
    (va, f_a) <- case s of
      Relevant -> do
        va_val <- cast a' a (PPropFst e) (val va')
        f_a <- f $$ VApp va_val
        (,f_a) <$> embedVal va_val
      Irrelevant -> do
        a'_prop <- freeze a'
        a_prop <- freeze a
        let va_prop = PCast a'_prop a_prop (PPropFst e) (prop va')
        f_a <- f $$ VAppProp va_prop
        pure (Prop va_prop, f_a)
      SortMeta s -> absurd s
    bindM4 cast (app b va) (app b' va') (pure (PApp (PPropSnd e) (prop va'))) (pure f_a)
  closureDefunEval (ClosureNaturalTransformation a b) vp = do
    a_p <- a $$ VApp (val vp)
    b_p <- b $$ VApp (val vp)
    pure (VPi Relevant Hole a_p (Lift b_p))
  closureDefunEval (ClosureFixFType x g env c) vp = do
    g_p <- g $$ VApp (val vp)
    pure (VPi Relevant x g_p (Closure (env :> (Bound, vp)) c))
  closureDefunEval (ClosureLiftViewInner t muF g view vp) vx = do
    x <- app t muF g muF view vp vx
    case x of
      VCons {} -> pure x
      x -> pure (VIn x)
  closureDefunEval (ClosureLiftView x t muF g view) vp =
    pure (VLambda Relevant x (Defun (ClosureLiftViewInner t muF g view vp)))

-- Test if two known head constructors are different
headNeq :: VTy -> VTy -> Bool
headNeq VNat VNat = False
headNeq (VPi {}) (VPi {}) = False
headNeq (VU {}) (VU {}) = False
headNeq (VSigma {}) (VSigma {}) = False
headNeq (VQuotient {}) (VQuotient {}) = False
headNeq (VId {}) (VId {}) = False
headNeq (VBox {}) (VBox {}) = False
headNeq VRUnit VRUnit = False
headNeq (VMu {}) (VMu {}) = False
headNeq t u = hasTypeHead t && hasTypeHead u
  where
    -- Test if type has reduced to know its head constructor
    hasTypeHead :: VTy -> Bool
    hasTypeHead VNat = True
    hasTypeHead (VPi {}) = True
    hasTypeHead (VU {}) = True
    hasTypeHead (VSigma {}) = True
    hasTypeHead (VQuotient {}) = True
    hasTypeHead (VId {}) = True
    hasTypeHead (VBox {}) = True
    hasTypeHead VRUnit = True
    hasTypeHead (VMu {}) = True
    hasTypeHead _ = False

eqReduce :: forall m. MonadEvaluator m => Val -> VTy -> Val -> m Val
eqReduce vt va vu = eqReduceType va
  where
    -- Initially driven just by the type
    eqReduceType :: VTy -> m Val
    -- Rule Eq-Fun
    eqReduceType (VPi s x a b) = do
      -- Γ ⊢ f ~[Π(x : A). B] g => Π(x : A). f x ~[B] g x
      -- Γ, x : A ⊢ f x ~[B] g x
      s_res <- resolveSort s
      pure (VPi s x a (Defun (ClosureEqFun s_res vt b vu)))
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
    eqReduceAll VRUnit (VU Relevant) VRUnit = pure VUnit
    eqReduceAll (VU s) (VU Relevant) (VU s')
      | s == s' = pure VUnit
      | otherwise = pure VEmpty
    -- Rule Eq-Π
    eqReduceAll (VPi s _ a b) (VU Relevant) (VPi s' x' a' b')
      | s == s' = do
          a'_eq_a <- eqReduce a' (VU s) a
          s_res <- resolveSort s
          pure (VExists (Name "$e") a'_eq_a (Defun (ClosureEqPi s_res x' a a' b b')))
    -- Rule Eq-Σ
    eqReduceAll (VSigma x a b) (VU Relevant) (VSigma _ a' b') = do
      a_eq_a' <- eqReduce a (VU Relevant) a'
      pure (VExists (Name "$e") a_eq_a' (Defun (ClosureEqSigma x a a' b b')))
    -- Rule Eq-Quotient
    eqReduceAll (VQuotient a x y r _ _ _ _ _ _ _ _ _ _ _ _) (VU Relevant) (VQuotient a' _ _ r' _ _ _ _ _ _ _ _ _ _ _ _) = do
      a_eq_a' <- eqReduce a (VU Relevant) a'
      pure (VExists (Name "$e") a_eq_a' (Defun (ClosureEqQuotient x y a a' r r')))
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
      t_entry <- embedVal t
      u <- p $$ VSnd
      t' <- p' $$ VFst
      t'_entry <- embedVal t'
      u' <- p' $$ VSnd
      t_eq_t' <- eqReduce t a t'
      pure (VExists (Name "$e") t_eq_t' (Defun (ClosureEqPair x b t_entry t'_entry u u')))
    -- Rule Quotient-Proj-Eq
    eqReduceAll (VQProj t) (VQuotient _ _ _ r _ _ _ _ _ _ _ _ _ _ _ _) (VQProj u) = do
      t <- embedVal t
      u <- embedVal u
      app r t u
    -- Rule Id-Eq
    eqReduceAll (VId {}) (VU Relevant) (VId {}) = undefined
    -- eqReduceAll (VId a t u) (VU Relevant) (VId a' t' u') = do
    --   a_eq_a' <- eqReduce a (VU Relevant) a'
    --   let t_eq_t' ve = do
    --         let env' = env :> (Bound, ve)
    --         bindM3 (eqReduce env') (cast a a' (prop ve) t) (pure a') (pure t')
    --       u_eq_u' ve = do
    --         let env'' = env :> (Bound, ve) & extend (level env + 1)
    --         bindM3 (eqReduce env'') (cast a a' (prop ve) u) (pure a') (pure u')
    --       t_eq_t'_and_u_eq_u' ve = VAnd <$> t_eq_t' ve <*> u_eq_u' ve
    --   VExists (Name "$e") a_eq_a' <$> makeFnClosure' t_eq_t'_and_u_eq_u'
    -- Rule Cons-Eq
    eqReduceAll (VCons c t _) (VMu tag f aty cs functor (Just _)) (VCons c' t' _)
      | c == c' = do
          case lookup c cs of
            Nothing -> error "BUG: Impossible (constructor not well typed in equality)"
            Just (_, bi, _) -> do
              let muF_val = VMu tag f aty cs functor Nothing
              muF <- embedVal muF_val
              b_muF_a <- app bi muF
              eqReduce t b_muF_a t'
      | otherwise = pure VEmpty
    -- Rule Mu-Eq
    eqReduceAll (VMu tag _ aTy _ _ (Just a)) (VU Relevant) (VMu tag' _ _ _ _ (Just a'))
      | tag == tag' = eqReduce a aTy a'
    -- Rule Box-Eq
    eqReduceAll (VBox a) (VU Relevant) (VBox b) =
      eqReduce a (VU Irrelevant) b
    -- Rule 1-Eq
    eqReduceAll _ VRUnit _ = pure VUnit
    -- Rule Box-Proof-Eq
    eqReduceAll (VBoxProof _) (VBox _) (VBoxProof _) = pure VUnit
    -- No reduction rule
    eqReduceAll t a u = pure (VEq t a u)

cast :: forall m. MonadEvaluator m => VTy -> VTy -> VProp -> Val -> m Val
-- Rule Cast-Zero
cast VNat VNat _ VZero = pure VZero
-- Rule Cast-Succ
cast VNat VNat e (VSucc n) = VSucc <$> cast VNat VNat e n
-- Rule Cast-Univ
cast (VU s) (VU s') _ a
  | s == s' = pure a
-- Rule Cast-Pi
cast (VPi s _ a b) (VPi _ x' a' b') e f = do
  s <- resolveSort s
  pure (VLambda s x' (Defun (ClosureCastPi s a a' b b' e f)))
cast (VSigma _ a b) (VSigma _ a' b') e (VPair t u) = do
  t'_val <- cast a a' (PPropFst e) t
  t' <- embedVal t'_val
  t <- embedVal t
  u' <- bindM4 cast (app b t) (app b' t') (pure (PApp (PPropSnd e) (prop t))) (pure u)
  pure (VPair t'_val u')
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
cast (VBox a) (VBox b) e (VBoxProof t) = do
  a_prop <- freeze a
  b_prop <- freeze b
  pure (VBoxProof (PCast a_prop b_prop e t))
cast VRUnit VRUnit _ t = pure t
cast (VMu tag f aty cs functor (Just a)) (VMu _ _ _ _ _ (Just a')) e (VCons ci t e') =
  case lookup ci cs of
    Nothing -> error "BUG: Impossible"
    Just (_, _, ixi) -> do
      let muF_val = VMu tag f aty cs functor Nothing
      muF <- embedVal muF_val
      a <- embedVal a
      a' <- embedVal a'
      t_entry <- embedVal t
      ixi_muF_t <- app ixi muF t_entry
      ixi_prop <- freeze ixi_muF_t
      pure (VCons ci t (PTrans ixi_prop (prop a) (prop a') e' e))
cast a b e t
  | headNeq a b = pure (VAbort b e)
  | otherwise = pure (VCast a b e t)

closure :: forall n m. MonadEvaluator m => Env -> Term Ix -> m (ValClosure n)
closure env t = pure (Closure env t)

evalSort :: MonadEvaluator m => Relevance -> m Relevance
evalSort Relevant = pure Relevant
evalSort Irrelevant = pure Irrelevant
evalSort (SortMeta m) = do
  s <- lookupSortMeta m
  case s of
    Just s -> evalSort s
    Nothing -> pure (SortMeta m)

eval :: forall m. MonadEvaluator m => Env -> Term Ix -> m Val
eval env (Var (Ix x)) = evalVar env x
  where
    evalVar (_ :> (_, Val v _)) 0 = pure v
    evalVar (env :> _) x = evalVar env (x - 1)
    evalVar _ _ = error "BUG: Impossible"
eval _ (U s) = VU <$> evalSort s
eval env (Lambda s x e) = pure (VLambda s x (Closure env e))
eval env (App Relevant t u) = elimM (eval env t) (VApp <$> eval env u)
eval env (App Irrelevant t u) = elimM (eval env t) (VAppProp <$> evalProp env u)
eval _ (App (SortMeta m) _ _) = absurd m
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
eval _ (PropPair {}) = error "BUG: impossible (eval on prop)"
eval _ (PropFst _) = error "BUG: impossible (eval on prop)"
eval _ (PropSnd _) = error "BUG: impossible (eval on prop)"
eval env (Exists x a b) = VExists x <$> eval env a <*> closure env b
eval env (Abort a t) = VAbort <$> eval env a <*> evalProp env t
eval _ Empty = pure VEmpty
eval _ One = error "BUG: impossible (eval on prop)"
eval _ Unit = pure VUnit
eval env (Eq t a u) = bindM3 eqReduce (eval env t) (eval env a) (eval env u)
eval _ (Refl _) = error "BUG: impossible (eval on prop)"
eval _ (Sym {}) = error "BUG: impossible (eval on prop)"
eval _ (Trans {}) = error "BUG: impossible (eval on prop)"
eval _ (Ap {}) = error "BUG: impossible (eval on prop)"
eval _ (Transp {}) = error "BUG: impossible (eval on prop)"
eval env (Cast a b e t) = bindM4 cast (eval env a) (eval env b) (evalProp env e) (eval env t)
eval env (Pair t u) = VPair <$> eval env t <*> eval env u
eval env (Fst p) = elimM (eval env p) (pure VFst)
eval env (Snd p) = elimM (eval env p) (pure VSnd)
eval env (Sigma x a b) = VSigma x <$> eval env a <*> closure env b
eval env (Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) = do
  a <- eval env a
  r <- closure env r
  rr <- propClosure env rr
  rs <- propClosure env rs
  rt <- propClosure env rt
  pure (VQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)
eval env (QProj t) = VQProj <$> eval env t
eval env (QElim z b x tpi px py pe p u) = do
  u <- eval env u
  b <- closure env b
  tpi <- closure env tpi
  p <- propClosure env p
  u $$ VQElim z b x tpi px py pe p
eval env (IdRefl t) = VIdRefl <$> eval env t
eval env (IdPath e) = VIdPath <$> evalProp env e
eval env (J a t x pf b u t' e) = do
  a <- eval env a
  t <- eval env t
  b <- closure env b
  u <- eval env u
  t' <- eval env t'
  e <- eval env e
  e $$ VJ a t x pf b u t'
eval env (Id a t u) = VId <$> eval env a <*> eval env t <*> eval env u
eval env (BoxProof e) = VBoxProof <$> evalProp env e
eval env (BoxElim t) = do
  t <- eval env t
  t $$ VBoxElim
eval env (Box a) = VBox <$> eval env a
eval _ ROne = pure VROne
eval _ RUnit = pure VRUnit
eval env (Cons c t e) = VCons c <$> eval env t <*> evalProp env e
-- [In] and witnesses the isomorphism [μF ≅ F[μF]] for inductive types.
-- Semantically, this is the identity, but must block when its argument is
-- neutral
eval env (In t) = do
  t <- eval env t
  case t of
    VCons c t e -> pure (VCons c t e)
    t -> pure (VIn t)
eval env (FLift f a) = do
  f <- eval env f
  a <- eval env a
  a_entry <- embedVal a
  case f of
    -- TODO: this tag is wrong and can cause issues
    VMu tag f' aty cs functor Nothing ->
      pure (functorLift tag f' aty cs functor a_entry)
    _ -> pure (VFLift f a)
eval env (Fmap f a b g p x) = do
  (f_entry, f) <- eval env f >>= embedVal'
  (a_entry, a) <- eval env a >>= embedVal'
  (b_entry, b) <- eval env b >>= embedVal'
  (g_entry, g) <- eval env g >>= embedVal'
  (p_entry, p) <- eval env p >>= embedVal'
  (x_entry, x) <- eval env x >>= embedVal'
  case f of
    VMu _ _ _ _ (Just (VFunctorInstance _ _ _ _ _ t)) Nothing ->
      app t f_entry a_entry b_entry g_entry p_entry x_entry
    _ -> pure (VFmap f a b g p x)
eval env (Match t x c bs) = do
  t <- eval env t
  c <- closure env c
  bs <- mapM (branch env) bs
  t $$ VMatch x c bs
  where
    branch :: Env -> (Name, Binder, Binder, Term Ix) -> m (Name, Binder, Binder, ValClosure (A 2))
    branch env (c, x, e, t) = (c,x,e,) <$> closure env t
eval env (FixedPoint i g v f p x c t) = do
  i <- eval env i
  c <- closure env c
  t <- closure env t
  pure (VFixedPoint i g v f p x c t Nothing)
eval env (Mu tag f t cs functor) = do
  t <- eval env t
  cs <- mapM (\(ci, xi, bi, _, ixi) -> (ci,) <$> ((xi,,) <$> closure env bi <*> closure env ixi)) cs
  functor <- mapM evalFunctor functor
  pure (VMu tag f t cs functor Nothing)
  where
    evalFunctor :: FunctorInstance Ix -> m VFunctorInstance
    evalFunctor (FunctorInstanceF a b f p x t) =
      VFunctorInstance a b f p x <$> closure env t
eval env (Let _ s _ t u) = do
  t <- eval' s env t
  eval (env :> (Defined, t)) u
eval env (Annotation t _) = eval env t
eval env (Meta mv) = do
  t <- lookupMeta mv
  case t of
    Nothing -> pure (VMeta mv env)
    Just solved -> eval env solved

functorLift
  :: Tag
  -> Name
  -> VTy
  -> [(Name, (Binder, ValClosure (A 1), ValClosure (A 2)))]
  -> Maybe VFunctorInstance
  -> EnvEntry
  -> VTy
functorLift tag f aty cs functor a =
  VMu tag f aty (map sub cs) functor Nothing
  where
    sub
      :: (Name, (Binder, ValClosure (A 1), ValClosure (A 2)))
      -> (Name, (Binder, ValClosure (A 1), ValClosure (A 2)))
    sub (ci, (xi, bi, ixi)) =
      (ci, (xi, SubstClosure a bi, SubstClosure a ixi))

match
  :: MonadEvaluator m
  => Binder
  -> ValClosure (A 1)
  -> Val
  -> [(Name, Binder, Binder, ValClosure (A 2))]
  -> m Val
match _ _ (VCons c u e) ((c', _, _, t) : _)
  | c == c' = do
      u <- embedVal u
      app t u (Prop e)
match x c t@(VCons {}) (_ : bs) = match x c t bs
match x c (VNeutral ne sp) bs = pure (VNeutral ne (sp :> VMatch x c bs))
match x c t bs = pure (neElim t (VMatch x c bs))

valIdentity :: MonadEvaluator m => Binder -> m Val
valIdentity x = do
  let idTm = Lambda Relevant Hole (Lambda Relevant x (Var 0))
  eval [] idTm

infixl 8 $$

($$) :: MonadEvaluator m => Val -> VElim -> m Val
(VLambda Relevant _ c) $$ (VApp u) = app c =<< embedVal u
(VLambda Irrelevant _ c) $$ (VAppProp p) = app c (Prop p)
-- Only reduce a fixed point [(fix f) ps a => f (fix f) ps a] when
-- [a] is a normal form; i.e. a constructor. This avoids the risk of
-- infinitely looping.
(VFixedPoint muF g v f p x c t (Just a)) $$ (VApp u@(VCons {})) = do
  let fix_f_val = VFixedPoint muF g v f p x c t Nothing
  muF <- embedVal muF
  fix_f <- embedVal fix_f_val
  a <- embedVal a
  u <- embedVal u
  -- This identity function holds in the empty context, so we create a syntactic
  -- form and then evaluate it in the empty environment to get a semantic identity
  -- function.
  vviewId_val <- valIdentity x
  vv <- embedVal vviewId_val
  app t muF vv fix_f a u
(VFixedPoint muF g v f p x c t Nothing) $$ (VApp u) =
  pure (VFixedPoint muF g v f p x c t (Just u))
(VMu tag f t cs functor Nothing) $$ (VApp a) = pure (VMu tag f t cs functor (Just a))
VZero $$ (VNElim _ _ t0 _ _ _) = pure t0
(VSucc n) $$ elim@(VNElim _ _ _ _ _ ts) = do
  r_val <- n $$ elim
  r <- embedVal r_val
  n <- embedVal n
  app ts n r
(VPair t _) $$ VFst = pure t
(VPair _ u) $$ VSnd = pure u
(VQProj t) $$ (VQElim _ _ _ tpi _ _ _ _) = app tpi =<< embedVal t
(VIdRefl _) $$ (VJ _ _ _ _ _ u _) = pure u
-- TODO: Currently a mess (as with other inductive equality stuff)
(VIdPath _) $$ (VJ {}) = undefined
-- (VIdPath _) $$ (VJ _ t _ _ b u t') = do
--   b_t_idrefl_t <- app b t (VIdRefl t)
--   b_t'_idpath_e <- app b t' VIdPath
--   env <- asks evalEnv
--   lvl <- asks evalLvl

--   let tm_t = quote lvl t
--       tm_t' = quote lvl t'
--       eqJ = Transp tm_t (Name "x") Hole (quote (lvl + 2) (app))
--   cast b_t_idrefl_t b_t'_idpath_e (VProp env eqJ) u
t $$ (VMatch x c bs) = match x c t bs
ne $$ u = pure (neElim ne u)

elimM :: MonadEvaluator m => m Val -> m VElim -> m Val
elimM = bindM2 ($$)

neElim :: Val -> VElim -> Val
neElim (VNeutral ne sp) u = VNeutral ne (sp :> u)
neElim ne u = VNeutral ne [u]

-- app :: MonadEvaluator m => ClosureApply m n cl Val => ValClosure n -> cl
-- app = app

quoteSp :: forall m. MonadEvaluator m => Lvl -> Term Ix -> VSpine -> m (Term Ix)
quoteSp _ base [] = pure base
quoteSp l base (sp :> VApp u) = App Relevant <$> quoteSp l base sp <*> quote l u
quoteSp l base (sp :> VAppProp p) = App Irrelevant <$> quoteSp l base sp <*> quoteProp l p
quoteSp l base (sp :> VNElim z a t0 x ih ts) =
  NElim z <$> a' <*> quote l t0 <*> pure x <*> pure ih <*> ts' <*> quoteSp l base sp
  where
    a', ts' :: m (Term Ix)
    a' = quote (l + 1) =<< app a (varR l)
    ts' = quote (l + 2) =<< app ts (varR l) (varR (l + 1))
quoteSp l base (sp :> VFst) = Fst <$> quoteSp l base sp
quoteSp l base (sp :> VSnd) = Snd <$> quoteSp l base sp
quoteSp l base (sp :> VQElim z b x tpi px py pe p) = do
  b <- quote (l + 1) =<< app b (varR l)
  tpi <- quote (l + 1) =<< app tpi (varR l)
  p <- quoteProp (l + 3) =<< app p (varP l) (varP (l + 1)) (varP (l + 2))
  QElim z b x tpi px py pe p <$> quoteSp l base sp
quoteSp l base (sp :> VJ a t x pf b u v) = do
  a <- quote l a
  t <- quote l t
  b <- quote (l + 2) =<< app b (varR l) (varR (l + 1))
  u <- quote l u
  v <- quote l v
  J a t x pf b u v <$> quoteSp l base sp
quoteSp l base (sp :> VBoxElim) = BoxElim <$> quoteSp l base sp
quoteSp l base (sp :> VMatch x c bs) = do
  c <- quote (l + 1) =<< app c (varR l)
  bs <- mapM quoteBranch bs
  sp <- quoteSp l base sp
  pure (Match sp x c bs)
  where
    quoteBranch :: (Name, Binder, Binder, ValClosure (A 2)) -> m (Name, Binder, Binder, Term Ix)
    quoteBranch (c, x, e, t) = (c,x,e,) <$> (quote (l + 2) =<< app t (varR l) (varR (l + 1)))

quote :: forall m. MonadEvaluator m => Lvl -> Val -> m (Term Ix)
quote lvl (VNeutral ne sp) = do
  ne <- quote lvl ne
  quoteSp lvl ne sp
quote lvl (VRigid x) = pure (Var (lvl2ix lvl x))
quote _ (VFlex mv _) = pure (Meta mv)
quote _ (VU s) = pure (U s)
quote lvl (VLambda s x t) = Lambda s x <$> (quote (lvl + 1) =<< app t (var s lvl))
quote lvl (VPi s x a b) = Pi s x <$> quote lvl a <*> (quote (lvl + 1) =<< app b (varR lvl))
quote _ VZero = pure Zero
quote lvl (VSucc t) = Succ <$> quote lvl t
quote _ VNat = pure Nat
quote lvl (VExists x a b) =
  Exists x <$> quote lvl a <*> (quote (lvl + 1) =<< app b (varR lvl))
quote lvl (VAbort a t) = Abort <$> quote lvl a <*> quoteProp lvl t
quote _ VEmpty = pure Empty
quote _ VUnit = pure Unit
quote lvl (VEq t a u) = Eq <$> quote lvl t <*> quote lvl a <*> quote lvl u
quote lvl (VCast a b e t) = Cast <$> quote lvl a <*> quote lvl b <*> quoteProp lvl e <*> quote lvl t
quote lvl (VPair t u) = Pair <$> quote lvl t <*> quote lvl u
quote lvl (VSigma x a b) =
  Sigma x <$> quote lvl a <*> (quote (lvl + 1) =<< app b (varR lvl))
quote lvl (VQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) = do
  a <- quote lvl a
  r <- quote (lvl + 2) =<< app r (varR lvl) (varR (lvl + 1))
  rr <- quoteProp (lvl + 1) =<< app rr (varP lvl)
  rs <- quoteProp (lvl + 3) =<< app rs (varP lvl) (varP (lvl + 1)) (varP (lvl + 2))
  rt <- quoteProp (lvl + 5) =<< app rt (varP lvl) (varP (lvl + 1)) (varP (lvl + 2)) (varP (lvl + 3)) (varP (lvl + 4))
  pure (Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)
quote lvl (VQProj t) = QProj <$> quote lvl t
quote lvl (VIdRefl t) = IdRefl <$> quote lvl t
quote lvl (VIdPath e) = IdPath <$> quoteProp lvl e
quote lvl (VId a t u) = Id <$> quote lvl a <*> quote lvl t <*> quote lvl u
quote lvl (VCons c t e) = Cons c <$> quote lvl t <*> quoteProp lvl e
quote lvl (VIn t) = In <$> quote lvl t
quote lvl (VBoxProof e) = BoxProof <$> quoteProp lvl e
quote lvl (VBox a) = Box <$> quote lvl a
quote _ VROne = pure ROne
quote _ VRUnit = pure RUnit
quote lvl (VFLift f a) = FLift <$> quote lvl f <*> quote lvl a
quote lvl (VFmap f a b g p x) =
  Fmap <$> quote lvl f <*> quote lvl a <*> quote lvl b <*> quote lvl g <*> quote lvl p <*> quote lvl x
quote lvl (VFixedPoint i g v f p x c t a) = do
  i <- quote lvl i
  c <- quote (lvl + 4) =<< app c (varR lvl) (varR (lvl + 1)) (varR (lvl + 2)) (varR (lvl + 3))
  t <- quote (lvl + 5) =<< app t (varR lvl) (varR (lvl + 1)) (varR (lvl + 2)) (varR (lvl + 3)) (varR (lvl + 4))
  let fix_f = FixedPoint i g v f p x c t
  case a of
    Nothing -> pure fix_f
    Just a -> App Relevant fix_f <$> quote lvl a
quote lvl (VMu tag f aty cs functor a) = do
  fty <- quote lvl aty
  let vf = varR lvl
      quoteCons
        :: (Name, (Binder, ValClosure (A 1), ValClosure (A 2)))
        -> m (Name, Binder, Type Ix, Name, Type Ix)
      quoteCons (ci, (xi, bi, ixi)) = do
        let vxi = varR (lvl + 1)
        bi_f <- app bi vf
        ixi_f_xi <- app ixi vf vxi
        (ci,xi,,f,) <$> quote (lvl + 1) bi_f <*> quote (lvl + 2) ixi_f_xi
  cs <- mapM quoteCons cs
  functor <- mapM quoteFunctor functor
  let muF = Mu tag f fty cs functor
  case a of
    Nothing -> pure muF
    Just a -> App Relevant muF <$> quote lvl a
  where
    quoteFunctor :: VFunctorInstance -> m (FunctorInstance Ix)
    quoteFunctor (VFunctorInstance a b f p x t) = do
      t <- quote (lvl + 6) =<< app t (varR lvl) (varR (lvl + 1)) (varR (lvl + 2)) (varR (lvl + 3)) (varR (lvl + 4)) (varR (lvl + 5))
      pure (FunctorInstanceF a b f p x t)

nbe :: MonadEvaluator m => Sort -> Env -> Term Ix -> m (Term Ix)
nbe Relevant env t = eval env t >>= quote (level env)
nbe Irrelevant env t = evalProp env t >>= quoteProp (level env)
nbe (SortMeta m) _ _ = absurd m
