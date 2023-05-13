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
  valToVProp,
  closureToVProp,
  quoteProp,
) where

import MonadEvaluator
import Syntax
import Value

instance MonadEvaluator m => ClosureEval m VProp where
  closureEval = evalProp
  closureDefunEval (ClosureEqFun f b g) v = do
    b_v <- app b v
    pure (PEq (PApp f (prop v)) b_v (PApp g (prop v)))
  closureDefunEval (ClosureEqPiFamily ve a a' b b') va' = do
    let va = PCast a' a (prop ve) (prop va')
    b_a <- app b (Prop va)
    b'_a' <- app b' va'
    pure (PEq b_a (PU Relevant) b'_a')
  closureDefunEval (ClosureEqPi s x a a' b b') ve =
    pure (PPi s x a' (Defun (ClosureEqPiFamily ve a a' b b')))
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
  closureDefunEval (ClosureCastPi a a' b b' e f) va' = do
    let va = PCast a' a (PPropFst e) (prop va')
    b_a <- app b (Prop va)
    b'_a' <- app b' va'
    pure (PCast b_a b'_a' (PApp (PPropSnd e) (prop va')) (PApp f va))

evalProp :: forall m. MonadEvaluator m => Env -> Term Ix -> m VProp
evalProp env (Var (Ix x)) = evalVar env x
  where
    evalVar (_ :> (_, p)) 0 = pure (prop p)
    evalVar (env :> _) x = evalVar env (x - 1)
    evalVar _ _ = error "BUG: Impossible"
evalProp _ (U s) = pure (PU s)
evalProp env (Lambda x t) = PLambda x <$> propClosure env t
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
evalProp env (Cons c t e) = PCons c <$> evalProp env t <*> evalProp env e
evalProp env (In t) = PIn <$> evalProp env t
evalProp env (FLift f a) = PFLift <$> evalProp env f <*> evalProp env a
evalProp env (FmapAny f a b g p x) = do
  f <- evalProp env f
  a <- evalProp env a
  b <- evalProp env b
  g <- evalProp env g
  p <- traverse (evalProp env) p
  x <- evalProp env x
  pure (PFmap f a b g p x)
evalProp env (MatchAny t x p bs) = do
  t <- evalProp env t
  p <- propClosure env p
  bs <- mapM evalBranch bs
  pure (PMatch t x p bs)
  where
    evalBranch :: (Name, Binder, Maybe Binder, Term Ix) -> m (Name, Binder, Maybe Binder, PropClosure (A 2))
    evalBranch (c, x, e, t) = (c,x,e,) <$> propClosure env t
evalProp env (FixedPointAny i g v f p x c t) = do
  i <- evalProp env i
  c <- propClosure env c
  t <- propClosure env t
  pure (PFixedPoint i g v f p x c t)
evalProp env (Mu tag f t x cs functor) = do
  t <- evalProp env t
  cs <- mapM evalCons cs
  functor <- mapM evalFunctor functor
  pure (PMu tag f t x cs functor)
  where
    evalCons
      :: (Name, Relevance, Binder, Term Ix, Name, Term Ix)
      -> m (Name, Relevance, Binder, PropClosure (A 2), PropClosure (A 3))
    evalCons (ci, si, xi, bi, _, ixi) = do
      bi <- propClosure env bi
      ixi <- propClosure env ixi
      pure (ci, si, xi, bi, ixi)

    evalFunctor :: FunctorInstance Ix -> m PFunctorInstance
    evalFunctor (FunctorInstanceF a b f p x t) =
      PFunctorInstance a b f p x <$> propClosure env t
evalProp env (Let x a t u) = do
  a <- evalProp env a
  t <- evalProp env t
  u <- propClosure env u
  pure (PLet x a t u)
evalProp env (Annotation t a) = PAnnotation <$> evalProp env t <*> evalProp env a
evalProp env (Meta m) = pure (PMeta m env)

propClosure :: MonadEvaluator m => Env -> Term Ix -> m (PropClosure n)
propClosure env t = pure (Closure env t)

spineToVProp :: forall m. MonadEvaluator m => VProp -> VSpine -> m VProp
spineToVProp base [] = pure base
spineToVProp base (sp :> VApp v) = do
  sp <- spineToVProp base sp
  v <- valToVProp v
  pure (PApp sp v)
spineToVProp base (sp :> VAppProp v) = do
  sp <- spineToVProp base sp
  pure (PApp sp v)
spineToVProp base (sp :> VNElim z a t0 x ih ts) = do
  sp <- spineToVProp base sp
  a <- closureToVProp a
  t0 <- valToVProp t0
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
  a <- valToVProp a
  t <- valToVProp t
  b <- closureToVProp b
  u <- valToVProp u
  t' <- valToVProp t'
  pure (PJ a t x pf b u t' sp)
spineToVProp base (sp :> VBoxElim) = PBoxElim <$> spineToVProp base sp
spineToVProp base (sp :> VMatch x p bs) = do
  sp <- spineToVProp base sp
  p <- closureToVProp p
  bs <- mapM branchToVProp bs
  pure (PMatch sp x p bs)
  where
    branchToVProp
      :: (Name, Binder, Binder, ValClosure (A 2))
      -> m (Name, Binder, Binder, PropClosure (A 2))
    branchToVProp (c, x, e, t) = (c,x,e,) <$> closureToVProp t
spineToVProp base (sp :> VMatchUniform x p bs) = do
  sp <- spineToVProp base sp
  p <- closureToVProp p
  bs <- mapM branchToVProp bs
  pure (PMatchUniform sp x p bs)
  where
    branchToVProp
      :: (Name, Binder, ValClosure (A 1))
      -> m (Name, Binder, PropClosure (A 1))
    branchToVProp (c, x, t) = (c,x,) <$> closureToVProp t

valToVProp :: forall m. MonadEvaluator m => Val -> m VProp
valToVProp (VNeutral ne sp) = do
  ne <- valToVProp ne
  spineToVProp ne sp
valToVProp (VRigid x) = pure (PVar x)
valToVProp (VFlex mv env) = pure (PMeta mv env)
valToVProp (VU s) = pure (PU s)
valToVProp (VLambda x t) = PLambda x <$> closureToVProp t
valToVProp (VPi s x a b) = PPi s x <$> valToVProp a <*> closureToVProp b
valToVProp VZero = pure PZero
valToVProp (VSucc n) = PSucc <$> valToVProp n
valToVProp VNat = pure PNat
valToVProp (VExists x a b) = PExists x <$> valToVProp a <*> closureToVProp b
valToVProp (VAbort a t) = PAbort <$> valToVProp a <*> pure t
valToVProp VEmpty = pure PEmpty
valToVProp VUnit = pure PUnit
valToVProp (VEq t a u) = PEq <$> valToVProp t <*> valToVProp a <*> valToVProp u
valToVProp (VCast a b e t) = PCast <$> valToVProp a <*> valToVProp b <*> pure e <*> valToVProp t
valToVProp (VPair t u) = PPair <$> valToVProp t <*> valToVProp u
valToVProp (VSigma x a b) = PSigma x <$> valToVProp a <*> closureToVProp b
valToVProp (VQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) = do
  a <- valToVProp a
  r <- closureToVProp r
  pure (PQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)
valToVProp (VQProj t) = PQProj <$> valToVProp t
valToVProp (VIdRefl t) = PIdRefl <$> valToVProp t
valToVProp (VIdPath e) = pure (PIdPath e)
valToVProp (VId a t u) = PId <$> valToVProp a <*> valToVProp t <*> valToVProp u
valToVProp (VCons c t e) = PCons c <$> valToVProp t <*> pure e
valToVProp (VFLift f a) = PFLift <$> valToVProp f <*> valToVProp a
valToVProp (VFmap f a b g p x) =
  PFmap <$> valToVProp f <*> valToVProp a <*> valToVProp b <*> valToVProp g <*> traverse valToVProp p <*> valToVProp x
valToVProp (VFixedPoint i g v f p x c t a) = do
  i <- valToVProp i
  c <- closureToVProp c
  t <- closureToVProp t
  let fp = PFixedPoint i g v f p x c t
  case a of
    Nothing -> pure fp
    Just (VAppR a) -> PApp fp <$> valToVProp a
    Just (VAppP a) -> pure (PApp fp a)
valToVProp (VMu tag f t x cs functor a) = do
  t <- valToVProp t
  cs <- mapM consToVProp cs
  functor <- mapM vFunctorToPFunctor functor
  let muF = PMu tag f t x cs functor
  case a of
    Nothing -> pure muF
    Just (VAppR a) -> PApp muF <$> valToVProp a
    Just (VAppP a) -> pure (PApp muF a)
  where
    consToVProp
      :: (Name, (Relevance, Binder, ValClosure (A 2), ValClosure (A 3)))
      -> m (Name, Relevance, Binder, PropClosure (A 2), PropClosure (A 3))
    consToVProp (ci, (si, xi, bi, ixi)) = do
      bi <- closureToVProp bi
      ixi <- closureToVProp ixi
      pure (ci, si, xi, bi, ixi)

    vFunctorToPFunctor :: VFunctorInstance -> m PFunctorInstance
    vFunctorToPFunctor (VFunctorInstance a b f p x t) =
      PFunctorInstance a b f p x <$> closureToVProp t
valToVProp (VBoxProof p) = pure (PBoxProof p)
valToVProp (VBox a) = PBox <$> valToVProp a

defunToVProp :: MonadEvaluator m => Defun Val -> m (Defun VProp)
defunToVProp (ClosureEqFun f b g) = ClosureEqFun <$> valToVProp f <*> closureToVProp b <*> valToVProp g
defunToVProp (ClosureEqPiFamily ve a a' b b') =
  ClosureEqPiFamily ve <$> valToVProp a <*> valToVProp a' <*> closureToVProp b <*> closureToVProp b'
defunToVProp (ClosureEqPi s x a a' b b') =
  ClosureEqPi s x <$> valToVProp a <*> valToVProp a' <*> closureToVProp b <*> closureToVProp b'
defunToVProp (ClosureEqSigmaFamily ve a a' b b') =
  ClosureEqSigmaFamily ve <$> valToVProp a <*> valToVProp a' <*> closureToVProp b <*> closureToVProp b'
defunToVProp (ClosureEqSigma x a a' b b') =
  ClosureEqSigma x <$> valToVProp a <*> valToVProp a' <*> closureToVProp b <*> closureToVProp b'
defunToVProp (ClosureEqQuotientY ve vx a a' r r') =
  ClosureEqQuotientY ve vx <$> valToVProp a <*> valToVProp a' <*> closureToVProp r <*> closureToVProp r'
defunToVProp (ClosureEqQuotientX ve y a a' r r') =
  ClosureEqQuotientX ve y <$> valToVProp a <*> valToVProp a' <*> closureToVProp r <*> closureToVProp r'
defunToVProp (ClosureEqQuotient x y a a' r r') =
  ClosureEqQuotient x y <$> valToVProp a <*> valToVProp a' <*> closureToVProp r <*> closureToVProp r'
defunToVProp (ClosureEqPair x b t t' u u') =
  ClosureEqPair x <$> closureToVProp b <*> pure t <*> pure t' <*> valToVProp u <*> valToVProp u'
defunToVProp (ClosureCastPi a a' b b' e f) =
  ClosureCastPi <$> valToVProp a <*> valToVProp a' <*> closureToVProp b <*> closureToVProp b' <*> pure e <*> valToVProp f

closureToVProp :: forall m n. MonadEvaluator m => ValClosure n -> m (PropClosure n)
closureToVProp (Closure env t) = pure (Closure env t)
closureToVProp (Lift v) = Lift <$> valToVProp v
closureToVProp (SubstClosure v cl) = SubstClosure v <$> closureToVProp cl
closureToVProp (DefunBase v defun) = DefunBase v <$> defunToVProp defun
closureToVProp (Defun defun) = Defun <$> defunToVProp defun

quoteProp :: forall m. MonadEvaluator m => Lvl -> VProp -> m (Term Ix)
quoteProp lvl (PVar x) = pure (Var (lvl2ix lvl x))
quoteProp _ (PMeta mv _) = pure (Meta mv)
quoteProp _ (PU s) = pure (U s)
quoteProp lvl (PLambda x t) = Lambda x <$> (quoteProp (lvl + 1) =<< app t (varP lvl))
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
quoteProp lvl (PCons c t e) = Cons c <$> quoteProp lvl t <*> quoteProp lvl e
quoteProp lvl (PIn t) = In <$> quoteProp lvl t
quoteProp lvl (POut t) = Out <$> quoteProp lvl t
quoteProp lvl (PFLift f a) = FLift <$> quoteProp lvl f <*> quoteProp lvl a
quoteProp lvl (PFmap f a b g (Just p) x) = do
  f <- quoteProp lvl f
  a <- quoteProp lvl a
  b <- quoteProp lvl b
  g <- quoteProp lvl g
  p <- quoteProp lvl p
  x <- quoteProp lvl x
  pure (Fmap f a b g p x)
quoteProp lvl (PFmap f a b g Nothing x) = do
  f <- quoteProp lvl f
  a <- quoteProp lvl a
  b <- quoteProp lvl b
  g <- quoteProp lvl g
  x <- quoteProp lvl x
  pure (FmapUniform f a b g x)
quoteProp lvl (PMatch t x p bs) = do
  t <- quoteProp lvl t
  p <- quoteProp (lvl + 1) =<< app p (varP lvl)
  bs <- mapM quoteBranch bs
  pure (Match t x p bs)
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
quoteProp lvl (PMu tag f t x cs functor) = do
  t <- quoteProp lvl t
  cs <- mapM quoteCons cs
  functor <- mapM quoteFunctor functor
  pure (Mu tag f t x cs functor)
  where
    quoteCons
      :: (Name, Relevance, Binder, PropClosure (A 2), PropClosure (A 3))
      -> m (Name, Relevance, Binder, Term Ix, Name, Term Ix)
    quoteCons (ci, si, xi, bi, ixi) = do
      bi <- quoteProp (lvl + 2) =<< app bi (varP lvl) (varP (lvl + 1))
      ixi <- quoteProp (lvl + 3) =<< app ixi (varP lvl) (varP (lvl + 1)) (varP (lvl + 2))
      pure (ci, si, xi, bi, f, ixi)

    quoteFunctor :: PFunctorInstance -> m (FunctorInstance Ix)
    quoteFunctor (PFunctorInstance a b f p x t) = do
      t <- quoteProp (lvl + 6) =<< app t (varP lvl) (varP (lvl + 1)) (varP (lvl + 2)) (varP (lvl + 3)) (varP (lvl + 4)) (varP (lvl + 5))
      pure (FunctorInstanceF a b f p x t)
quoteProp lvl (PLet x a t u) = do
  a <- quoteProp lvl a
  t <- quoteProp lvl t
  u <- quoteProp (lvl + 1) =<< app u (varP lvl)
  pure (Let x a t u)
quoteProp lvl (PAnnotation t a) = Annotation <$> quoteProp lvl t <*> quoteProp lvl a
