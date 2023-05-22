{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module EvalProp (
  evalProp,
  propClosure,
  freeze,
  closureToVProp,
  quoteProp,
  resolveSort,
) where

import MonadEvaluator
import Syntax
import Value

import Data.Void

resolveSort :: MonadEvaluator m => Relevance -> m Sort
resolveSort Relevant = pure Relevant
resolveSort Irrelevant = pure Irrelevant
resolveSort (SortMeta m) = do
  s <- lookupSortMeta m
  case s of
    Just s -> resolveSort s
    Nothing -> error "BUG"

instance MonadEvaluator m => ClosureEval m VProp where
  closureEval = evalProp
  closureDefunEval (ClosureEqFun _ f b g) v = do
    b_v <- app b v
    pure (PEq (PApp f (prop v)) b_v (PApp g (prop v)))
  closureDefunEval (ClosureEqPiFamily _ ve a a' b b') va' = do
    let va = PCast a' a (prop ve) (prop va')
    b_a <- app b (Prop va)
    b'_a' <- app b' va'
    pure (PEq b_a (PU Relevant) b'_a')
  closureDefunEval (ClosureEqPi s x a a' b b') ve =
    pure (PPi (fmap absurd s) x a' (Defun (ClosureEqPiFamily s ve a a' b b')))
  closureDefunEval (ClosureEqSigmaFamily ve a a' b b') va = do
    let va' = PCast a a' (prop ve) (prop va)
    b_a <- app b va
    b'_a' <- app b' (Prop va')
    pure (PEq b_a (PU Relevant) b'_a')
  closureDefunEval (ClosureEqSigma x a a' b b') ve =
    pure (PPi Relevant x a (Defun (ClosureEqSigmaFamily ve a a' b b')))
  closureDefunEval (ClosureEqQuotientY ve vx a a' r r') vy = do
    let vx' = PCast a a' (prop ve) (prop vx)
        vy' = PCast a a' (prop ve) (prop vy)
    r_x_y <- app r vx vy
    r'_x'_y' <- app r' (Prop vx') (Prop vy')
    pure (PEq r_x_y (PU Irrelevant) r'_x'_y')
  closureDefunEval (ClosureEqQuotientX ve y a a' r r') vx = do
    pure (PPi Relevant y a (Defun (ClosureEqQuotientY ve vx a a' r r')))
  closureDefunEval (ClosureEqQuotient x y a a' r r') ve = do
    pure (PPi Relevant x a (Defun (ClosureEqQuotientX ve y a a' r r')))
  closureDefunEval (ClosureEqPair x b t t' u u') ve = do
    let ap_B_e = PAp (PU Relevant) x b (prop t) (prop t') (prop ve)
    b_t <- app b t
    b_t' <- app b t'
    let cast_b_t_b_t'_u = PCast b_t b_t' ap_B_e u
    pure (PEq cast_b_t_b_t'_u b_t' u')
  closureDefunEval (ClosureCastPi _ a a' b b' e f) va' = do
    let va = PCast a' a (PPropFst e) (prop va')
    b_a <- app b (Prop va)
    b'_a' <- app b' va'
    pure (PCast b_a b'_a' (PApp (PPropSnd e) (prop va')) (PApp f va))
  closureDefunEval (ClosureNaturalTransformation a b) vp = do
    let a_p = PApp a (prop vp)
        b_p = PApp b (prop vp)
    pure (PPi Relevant Hole a_p (Lift b_p))
  closureDefunEval (ClosureFixFType x g env c) vp = do
    let g_p = PApp g (prop vp)
    pure (PPi Relevant x g_p (Closure (env :> (Bound, vp)) c))
  closureDefunEval (ClosureLiftViewInner t muF g view vp) vx = do
    PIn <$> app t muF g muF view vp vx
  closureDefunEval (ClosureLiftView x t muF g view) vp =
    pure (PLambda Relevant x (Defun (ClosureLiftViewInner t muF g view vp)))

evalProp :: forall m. MonadEvaluator m => Env -> Term Ix -> m VProp
evalProp env (Var (Ix x)) = evalVar env x
  where
    evalVar (_ :> (_, p)) 0 = pure (prop p)
    evalVar (env :> _) x = evalVar env (x - 1)
    evalVar _ _ = error "BUG: Impossible"
evalProp _ (U s) = pure (PU s)
evalProp env (Lambda s x t) = PLambda s x <$> propClosure env t
-- For evaluating applications with prop codomain, we don't care whether the argument
-- is a prop or not; we always compute a prop
evalProp env (App _ t u) = PApp <$> evalProp env t <*> evalProp env u
evalProp env (Pi s x a b) = PPi s x <$> evalProp env a <*> propClosure env b
evalProp _ Zero = pure PZero
evalProp env (Succ n) = PSucc <$> evalProp env n
evalProp env (NElim z a t0 x ih ts n) = do
  a <- propClosure env a
  t0 <- evalProp env t0
  ts <- propClosure env ts
  n <- evalProp env n
  pure (PNElim z a t0 x ih ts n)
evalProp _ Nat = pure PNat
evalProp env (PropPair t u) = PPropPair <$> evalProp env t <*> evalProp env u
evalProp env (PropFst t) = PPropFst <$> evalProp env t
evalProp env (PropSnd t) = PPropSnd <$> evalProp env t
evalProp env (Exists x a b) = PExists x <$> evalProp env a <*> propClosure env b
evalProp env (Abort a t) = PAbort <$> evalProp env a <*> evalProp env t
evalProp _ Empty = pure PEmpty
evalProp _ One = pure POne
evalProp _ Unit = pure PUnit
evalProp env (Eq t a u) = PEq <$> evalProp env t <*> evalProp env a <*> evalProp env u
evalProp env (Refl t) = PRefl <$> evalProp env t
evalProp env (Sym t u e) = PSym <$> evalProp env t <*> evalProp env u <*> evalProp env e
evalProp env (Trans t u v e e') =
  PTrans <$> evalProp env t <*> evalProp env u <*> evalProp env v <*> evalProp env e <*> evalProp env e'
evalProp env (Ap b x t u v e) = do
  b <- evalProp env b
  t <- propClosure env t
  u <- evalProp env u
  v <- evalProp env v
  e <- evalProp env e
  pure (PAp b x t u v e)
evalProp env (Transp t x pf b u t' e) = do
  t <- evalProp env t
  b <- propClosure env b
  u <- evalProp env u
  t' <- evalProp env t'
  e <- evalProp env e
  pure (PTransp t x pf b u t' e)
evalProp env (Cast a b e t) =
  PCast <$> evalProp env a <*> evalProp env b <*> evalProp env e <*> evalProp env t
evalProp env (Pair t u) = PPair <$> evalProp env t <*> evalProp env u
evalProp env (Fst t) = PFst <$> evalProp env t
evalProp env (Snd t) = PSnd <$> evalProp env t
evalProp env (Sigma x a b) = PSigma x <$> evalProp env a <*> propClosure env b
evalProp env (Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) = do
  a <- evalProp env a
  r <- propClosure env r
  rr <- propClosure env rr
  rs <- propClosure env rs
  rt <- propClosure env rt
  pure (PQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)
evalProp env (QProj t) = PQProj <$> evalProp env t
evalProp env (QElim z b x tpi px py pe p u) = do
  b <- propClosure env b
  tpi <- propClosure env tpi
  p <- propClosure env p
  u <- evalProp env u
  pure (PQElim z b x tpi px py pe p u)
evalProp env (IdRefl t) = PIdRefl <$> evalProp env t
evalProp env (IdPath e) = PIdPath <$> evalProp env e
evalProp env (J a t x pf b u t' e) = do
  a <- evalProp env a
  t <- evalProp env t
  b <- propClosure env b
  u <- evalProp env u
  t' <- evalProp env t'
  e <- evalProp env e
  pure (PJ a t x pf b u t' e)
evalProp env (Id a t u) = PId <$> evalProp env a <*> evalProp env t <*> evalProp env u
evalProp env (BoxProof t) = PBoxProof <$> evalProp env t
evalProp env (BoxElim t) = PBoxElim <$> evalProp env t
evalProp env (Box a) = PBox <$> evalProp env a
evalProp _ ROne = pure PROne
evalProp _ RUnit = pure PRUnit
evalProp env (Cons c t e) = PCons c <$> evalProp env t <*> evalProp env e
evalProp env (In t) = PIn <$> evalProp env t
evalProp env (FLift f a) = PFLift <$> evalProp env f <*> evalProp env a
evalProp env (Fmap f a b g p x) = do
  f <- evalProp env f
  a <- evalProp env a
  b <- evalProp env b
  g <- evalProp env g
  p <- evalProp env p
  x <- evalProp env x
  pure (PFmap f a b g p x)
evalProp env (Match t x c bs) = do
  t <- evalProp env t
  c <- propClosure env c
  bs <- mapM evalBranch bs
  pure (PMatch t x c bs)
  where
    evalBranch :: (Name, Binder, Binder, Term Ix) -> m (Name, Binder, Binder, PropClosure (A 2))
    evalBranch (c, x, e, t) = (c,x,e,) <$> propClosure env t
evalProp env (FixedPoint i g v f p x c t) = do
  i <- evalProp env i
  c <- propClosure env c
  t <- propClosure env t
  pure (PFixedPoint i g v f p x c t)
evalProp env (Mu tag f t cs functor) = do
  t <- evalProp env t
  cs <- mapM evalCons cs
  functor <- mapM evalFunctor functor
  pure (PMu tag f t cs functor)
  where
    evalCons
      :: (Name, Binder, Term Ix, Name, Term Ix)
      -> m (Name, Binder, PropClosure (A 1), PropClosure (A 2))
    evalCons (ci, xi, bi, _, ixi) = do
      bi <- propClosure env bi
      ixi <- propClosure env ixi
      pure (ci, xi, bi, ixi)

    evalFunctor :: FunctorInstance Ix -> m PFunctorInstance
    evalFunctor (FunctorInstanceF a b f p x t) =
      PFunctorInstance a b f p x <$> propClosure env t
evalProp env (Let x s a t u) = do
  a <- mapM (evalProp env) a
  t <- evalProp env t
  u <- propClosure env u
  pure (PLet x s a t u)
evalProp env (Annotation t a) = PAnnotation <$> evalProp env t <*> evalProp env a
evalProp env (Meta mv) = do
  t <- lookupMeta mv
  case t of
    Nothing -> pure (PMeta mv env)
    Just solved -> evalProp env solved

propClosure :: MonadEvaluator m => Env -> Term Ix -> m (PropClosure n)
propClosure env t = pure (Closure env t)

spineToVProp :: forall m. MonadEvaluator m => VProp -> VSpine -> m VProp
spineToVProp base [] = pure base
spineToVProp base (sp :> VApp v) = do
  sp <- spineToVProp base sp
  v <- freeze v
  pure (PApp sp v)
spineToVProp base (sp :> VAppProp v) = do
  sp <- spineToVProp base sp
  pure (PApp sp v)
spineToVProp base (sp :> VNElim z a t0 x ih ts) = do
  sp <- spineToVProp base sp
  a <- closureToVProp a
  t0 <- freeze t0
  ts <- closureToVProp ts
  pure (PNElim z a t0 x ih ts sp)
spineToVProp base (sp :> VFst) = PFst <$> spineToVProp base sp
spineToVProp base (sp :> VSnd) = PSnd <$> spineToVProp base sp
spineToVProp base (sp :> VQElim z b x tpi px py pe p) = do
  sp <- spineToVProp base sp
  b <- closureToVProp b
  tpi <- closureToVProp tpi
  pure (PQElim z b x tpi px py pe p sp)
spineToVProp base (sp :> VJ a t x pf b u t') = do
  sp <- spineToVProp base sp
  a <- freeze a
  t <- freeze t
  b <- closureToVProp b
  u <- freeze u
  t' <- freeze t'
  pure (PJ a t x pf b u t' sp)
spineToVProp base (sp :> VBoxElim) = PBoxElim <$> spineToVProp base sp
spineToVProp base (sp :> VMatch x c bs) = do
  sp <- spineToVProp base sp
  c <- closureToVProp c
  bs <- mapM branchToVProp bs
  pure (PMatch sp x c bs)
  where
    branchToVProp
      :: (Name, Binder, Binder, ValClosure (A 2))
      -> m (Name, Binder, Binder, PropClosure (A 2))
    branchToVProp (c, x, e, t) = (c,x,e,) <$> closureToVProp t

freeze :: forall m. MonadEvaluator m => Val -> m VProp
freeze (VNeutral ne sp) = do
  ne <- freeze ne
  spineToVProp ne sp
freeze (VRigid x) = pure (PVar x)
freeze (VFlex mv env) = pure (PMeta mv env)
freeze (VU s) = pure (PU s)
freeze (VLambda s x t) = PLambda s x <$> closureToVProp t
freeze (VPi s x a b) = PPi s x <$> freeze a <*> closureToVProp b
freeze VZero = pure PZero
freeze (VSucc n) = PSucc <$> freeze n
freeze VNat = pure PNat
freeze (VExists x a b) = PExists x <$> freeze a <*> closureToVProp b
freeze (VAbort a t) = PAbort <$> freeze a <*> pure t
freeze VEmpty = pure PEmpty
freeze VUnit = pure PUnit
freeze (VEq t a u) = PEq <$> freeze t <*> freeze a <*> freeze u
freeze (VCast a b e t) = PCast <$> freeze a <*> freeze b <*> pure e <*> freeze t
freeze (VPair t u) = PPair <$> freeze t <*> freeze u
freeze (VSigma x a b) = PSigma x <$> freeze a <*> closureToVProp b
freeze (VQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) = do
  a <- freeze a
  r <- closureToVProp r
  pure (PQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)
freeze (VQProj t) = PQProj <$> freeze t
freeze (VIdRefl t) = PIdRefl <$> freeze t
freeze (VIdPath e) = pure (PIdPath e)
freeze (VId a t u) = PId <$> freeze a <*> freeze t <*> freeze u
freeze (VBoxProof p) = pure (PBoxProof p)
freeze (VBox a) = PBox <$> freeze a
freeze VROne = pure PROne
freeze VRUnit = pure PRUnit
freeze (VCons c t e) = PCons c <$> freeze t <*> pure e
freeze (VIn t) = PIn <$> freeze t
freeze (VFLift f a) = PFLift <$> freeze f <*> freeze a
freeze (VFmap f a b g p x) =
  PFmap <$> freeze f <*> freeze a <*> freeze b <*> freeze g <*> freeze p <*> freeze x
freeze (VFixedPoint i g v f p x c t a) = do
  i <- freeze i
  c <- closureToVProp c
  t <- closureToVProp t
  let fp = PFixedPoint i g v f p x c t
  case a of
    Nothing -> pure fp
    Just a -> PApp fp <$> freeze a
freeze (VMu tag f t cs functor a) = do
  t <- freeze t
  cs <- mapM consToVProp cs
  functor <- mapM vFunctorToPFunctor functor
  let muF = PMu tag f t cs functor
  case a of
    Nothing -> pure muF
    Just a -> PApp muF <$> freeze a
  where
    consToVProp
      :: (Name, (Binder, ValClosure (A 1), ValClosure (A 2)))
      -> m (Name, Binder, PropClosure (A 1), PropClosure (A 2))
    consToVProp (ci, (xi, bi, ixi)) = do
      bi <- closureToVProp bi
      ixi <- closureToVProp ixi
      pure (ci, xi, bi, ixi)

    vFunctorToPFunctor :: VFunctorInstance -> m PFunctorInstance
    vFunctorToPFunctor (VFunctorInstance a b f p x t) =
      PFunctorInstance a b f p x <$> closureToVProp t

defunToVProp :: MonadEvaluator m => Defun Val -> m (Defun VProp)
defunToVProp (ClosureEqFun s f b g) = ClosureEqFun s <$> freeze f <*> closureToVProp b <*> freeze g
defunToVProp (ClosureEqPiFamily s ve a a' b b') =
  ClosureEqPiFamily s ve <$> freeze a <*> freeze a' <*> closureToVProp b <*> closureToVProp b'
defunToVProp (ClosureEqPi s x a a' b b') =
  ClosureEqPi s x <$> freeze a <*> freeze a' <*> closureToVProp b <*> closureToVProp b'
defunToVProp (ClosureEqSigmaFamily ve a a' b b') =
  ClosureEqSigmaFamily ve <$> freeze a <*> freeze a' <*> closureToVProp b <*> closureToVProp b'
defunToVProp (ClosureEqSigma x a a' b b') =
  ClosureEqSigma x <$> freeze a <*> freeze a' <*> closureToVProp b <*> closureToVProp b'
defunToVProp (ClosureEqQuotientY ve vx a a' r r') =
  ClosureEqQuotientY ve vx <$> freeze a <*> freeze a' <*> closureToVProp r <*> closureToVProp r'
defunToVProp (ClosureEqQuotientX ve y a a' r r') =
  ClosureEqQuotientX ve y <$> freeze a <*> freeze a' <*> closureToVProp r <*> closureToVProp r'
defunToVProp (ClosureEqQuotient x y a a' r r') =
  ClosureEqQuotient x y <$> freeze a <*> freeze a' <*> closureToVProp r <*> closureToVProp r'
defunToVProp (ClosureEqPair x b t t' u u') =
  ClosureEqPair x <$> closureToVProp b <*> pure t <*> pure t' <*> freeze u <*> freeze u'
defunToVProp (ClosureCastPi s a a' b b' e f) =
  ClosureCastPi s <$> freeze a <*> freeze a' <*> closureToVProp b <*> closureToVProp b' <*> pure e <*> freeze f
defunToVProp (ClosureNaturalTransformation a b) =
  ClosureNaturalTransformation <$> freeze a <*> freeze b
defunToVProp (ClosureFixFType x g env c) =
  ClosureFixFType x <$> freeze g <*> pure env <*> pure c
defunToVProp (ClosureLiftViewInner t muF g view vp) =
  ClosureLiftViewInner <$> closureToVProp t <*> pure muF <*> pure g <*> pure view <*> pure vp
defunToVProp (ClosureLiftView x t muF g view) =
  ClosureLiftView x <$> closureToVProp t <*> pure muF <*> pure g <*> pure view

closureToVProp :: forall m n. MonadEvaluator m => ValClosure n -> m (PropClosure n)
closureToVProp (Closure env t) = pure (Closure env t)
closureToVProp (Lift v) = Lift <$> freeze v
closureToVProp (SubstClosure v cl) = SubstClosure v <$> closureToVProp cl
closureToVProp (DefunBase v defun) = DefunBase v <$> defunToVProp defun
closureToVProp (Defun defun) = Defun <$> defunToVProp defun

quoteProp :: forall m. MonadEvaluator m => Lvl -> VProp -> m (Term Ix)
quoteProp lvl (PVar x) = pure (Var (lvl2ix lvl x))
quoteProp _ (PMeta mv _) = pure (Meta mv)
quoteProp _ (PU s) = pure (U s)
quoteProp lvl (PLambda s x t) = Lambda s x <$> (quoteProp (lvl + 1) =<< app t (varP lvl))
quoteProp lvl (PApp t u) = App Irrelevant <$> quoteProp lvl t <*> quoteProp lvl u
quoteProp lvl (PPi s x a b) = Pi s x <$> quoteProp lvl a <*> (quoteProp (lvl + 1) =<< app b (varP lvl))
quoteProp _ PZero = pure Zero
quoteProp lvl (PSucc n) = Succ <$> quoteProp lvl n
quoteProp lvl (PNElim z a t0 x ih ts n) = do
  a <- quoteProp (lvl + 1) =<< app a (varP lvl)
  t0 <- quoteProp lvl t0
  ts <- quoteProp (lvl + 2) =<< app ts (varP lvl) (varP (lvl + 1))
  n <- quoteProp lvl n
  pure (NElim z a t0 x ih ts n)
quoteProp _ PNat = pure Nat
quoteProp lvl (PPropPair t u) = PropPair <$> quoteProp lvl t <*> quoteProp lvl u
quoteProp lvl (PPropFst t) = PropFst <$> quoteProp lvl t
quoteProp lvl (PPropSnd t) = PropSnd <$> quoteProp lvl t
quoteProp lvl (PExists x a b) = Exists x <$> quoteProp lvl a <*> (quoteProp (lvl + 1) =<< app b (varP lvl))
quoteProp lvl (PAbort a t) = Abort <$> quoteProp lvl a <*> quoteProp lvl t
quoteProp _ PEmpty = pure Empty
quoteProp _ POne = pure One
quoteProp _ PUnit = pure Unit
quoteProp lvl (PEq t a u) = Eq <$> quoteProp lvl t <*> quoteProp lvl a <*> quoteProp lvl u
quoteProp lvl (PRefl t) = Refl <$> quoteProp lvl t
quoteProp lvl (PSym t u e) = Sym <$> quoteProp lvl t <*> quoteProp lvl u <*> quoteProp lvl e
quoteProp lvl (PTrans t u v e e') =
  Trans <$> quoteProp lvl t <*> quoteProp lvl u <*> quoteProp lvl v <*> quoteProp lvl e <*> quoteProp lvl e'
quoteProp lvl (PAp b x t u v e) = do
  b <- quoteProp lvl b
  t <- quoteProp (lvl + 1) =<< app t (varP lvl)
  u <- quoteProp lvl u
  v <- quoteProp lvl v
  e <- quoteProp lvl e
  pure (Ap b x t u v e)
quoteProp lvl (PTransp t x pf b u t' e) = do
  t <- quoteProp lvl t
  b <- quoteProp (lvl + 2) =<< app b (varP lvl) (varP (lvl + 1))
  u <- quoteProp lvl u
  t' <- quoteProp lvl t'
  e <- quoteProp lvl e
  pure (Transp t x pf b u t' e)
quoteProp lvl (PCast a b e t) = do
  a <- quoteProp lvl a
  b <- quoteProp lvl b
  e <- quoteProp lvl e
  t <- quoteProp lvl t
  pure (Cast a b e t)
quoteProp lvl (PPair t u) = Pair <$> quoteProp lvl t <*> quoteProp lvl u
quoteProp lvl (PFst t) = Fst <$> quoteProp lvl t
quoteProp lvl (PSnd t) = Snd <$> quoteProp lvl t
quoteProp lvl (PSigma x a b) = Sigma x <$> quoteProp lvl a <*> (quoteProp (lvl + 1) =<< app b (varP lvl))
quoteProp lvl (PQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) = do
  a <- quoteProp lvl a
  r <- quoteProp (lvl + 2) =<< app r (varP lvl) (varP (lvl + 1))
  rr <- quoteProp (lvl + 1) =<< app rr (varP lvl)
  rs <- quoteProp (lvl + 3) =<< app rs (varP lvl) (varP (lvl + 1)) (varP (lvl + 2))
  rt <- quoteProp (lvl + 5) =<< app rt (varP lvl) (varP (lvl + 1)) (varP (lvl + 2)) (varP (lvl + 3)) (varP (lvl + 4))
  pure (Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)
quoteProp lvl (PQProj t) = QProj <$> quoteProp lvl t
quoteProp lvl (PQElim z b x tpi px py pe p u) = do
  b <- quoteProp (lvl + 1) =<< app b (varP lvl)
  tpi <- quoteProp (lvl + 1) =<< app tpi (varP lvl)
  p <- quoteProp (lvl + 3) =<< app p (varP lvl) (varP (lvl + 1)) (varP (lvl + 2))
  u <- quoteProp lvl u
  pure (QElim z b x tpi px py pe p u)
quoteProp lvl (PIdRefl t) = IdRefl <$> quoteProp lvl t
quoteProp lvl (PIdPath e) = IdPath <$> quoteProp lvl e
quoteProp lvl (PJ a t x pf b u v e) = do
  a <- quoteProp lvl a
  t <- quoteProp lvl t
  b <- quoteProp (lvl + 2) =<< app b (varP lvl) (varP (lvl + 1))
  u <- quoteProp lvl u
  v <- quoteProp lvl v
  e <- quoteProp lvl e
  pure (J a t x pf b u v e)
quoteProp lvl (PId a t u) = Id <$> quoteProp lvl a <*> quoteProp lvl t <*> quoteProp lvl u
quoteProp lvl (PBoxProof e) = BoxProof <$> quoteProp lvl e
quoteProp lvl (PBoxElim t) = BoxElim <$> quoteProp lvl t
quoteProp lvl (PBox a) = Box <$> quoteProp lvl a
quoteProp _ PROne = pure ROne
quoteProp _ PRUnit = pure RUnit
quoteProp lvl (PCons c t e) = Cons c <$> quoteProp lvl t <*> quoteProp lvl e
quoteProp lvl (PIn t) = In <$> quoteProp lvl t
quoteProp lvl (PFLift f a) = FLift <$> quoteProp lvl f <*> quoteProp lvl a
quoteProp lvl (PFmap f a b g p x) = do
  f <- quoteProp lvl f
  a <- quoteProp lvl a
  b <- quoteProp lvl b
  g <- quoteProp lvl g
  p <- quoteProp lvl p
  x <- quoteProp lvl x
  pure (Fmap f a b g p x)
quoteProp lvl (PMatch t x c bs) = do
  t <- quoteProp lvl t
  c <- quoteProp (lvl + 1) =<< app c (varP lvl)
  bs <- mapM quoteBranch bs
  pure (Match t x c bs)
  where
    quoteBranch
      :: (Name, Binder, Binder, PropClosure (A 2))
      -> m (Name, Binder, Binder, Term Ix)
    quoteBranch (c, x, e, t) = (c,x,e,) <$> (quoteProp (lvl + 2) =<< app t (varP lvl) (varP (lvl + 1)))
quoteProp lvl (PFixedPoint i g v f p x c t) = do
  i <- quoteProp lvl i
  c <- quoteProp (lvl + 4) =<< app c (varP lvl) (varP (lvl + 1)) (varP (lvl + 2)) (varP (lvl + 3))
  t <- quoteProp (lvl + 5) =<< app t (varP lvl) (varP (lvl + 1)) (varP (lvl + 2)) (varP (lvl + 3)) (varP (lvl + 4))
  pure (FixedPoint i g v f p x c t)
quoteProp lvl (PMu tag f t cs functor) = do
  t <- quoteProp lvl t
  cs <- mapM quoteCons cs
  functor <- mapM quoteFunctor functor
  pure (Mu tag f t cs functor)
  where
    quoteCons
      :: (Name, Binder, PropClosure (A 1), PropClosure (A 2))
      -> m (Name, Binder, Term Ix, Name, Term Ix)
    quoteCons (ci, xi, bi, ixi) = do
      bi <- quoteProp (lvl + 1) =<< app bi (varP lvl)
      ixi <- quoteProp (lvl + 2) =<< app ixi (varP lvl) (varP (lvl + 1))
      pure (ci, xi, bi, f, ixi)

    quoteFunctor :: PFunctorInstance -> m (FunctorInstance Ix)
    quoteFunctor (PFunctorInstance a b f p x t) = do
      t <- quoteProp (lvl + 6) =<< app t (varP lvl) (varP (lvl + 1)) (varP (lvl + 2)) (varP (lvl + 3)) (varP (lvl + 4)) (varP (lvl + 5))
      pure (FunctorInstanceF a b f p x t)
quoteProp lvl (PLet x s a t u) = do
  a <- mapM (quoteProp lvl) a
  t <- quoteProp lvl t
  u <- quoteProp (lvl + 1) =<< app u (varP lvl)
  pure (Let x s a t u)
quoteProp lvl (PAnnotation t a) = Annotation <$> quoteProp lvl t <*> quoteProp lvl a
