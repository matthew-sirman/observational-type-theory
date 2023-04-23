{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module EvalProp (
  evalProp,
  evalProp',
  appProp,
  propClosure,
  propClosure',
  valToVProp,
  closureToVProp,
  envToPropEnv,
  quoteProp,
) where

import MonadEvaluator
import Syntax
import Value

import Data.Bifunctor (second)

evalProp :: forall m. MonadEvaluator m => Env VProp -> Term Ix -> m VProp
evalProp env (Var (Ix x)) = pure (snd (env !! x))
evalProp _ (U s) = pure (PU s)
evalProp env (Lambda x t) = PLambda x <$> propClosure env t
evalProp env (App t u) = PApp <$> evalProp env t <*> evalProp env u
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
evalProp env (Out t) = POut <$> evalProp env t
evalProp env (FLift f a) = PFLift <$> evalProp env f <*> evalProp env a
evalProp env (Fmap f a b g p x) = do
  f <- evalProp env f
  a <- evalProp env a
  b <- evalProp env b
  g <- evalProp env g
  p <- evalProp env p
  x <- evalProp env x
  pure (PFmap f a b g p x)
evalProp env (Match t x p bs) = do
  t <- evalProp env t
  p <- propClosure env p
  bs <- mapM evalBranch bs
  pure (PMatch t x p bs)
  where
    evalBranch :: (Name, Binder, Binder, Term Ix) -> m (Name, Binder, Binder, PropClosure (A 2))
    evalBranch (c, x, e, t) = (c,x,e,) <$> propClosure env t
evalProp env (FixedPoint i g v f p x c t) = do
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

evalProp' :: MonadEvaluator m => Env ValProp -> Term Ix -> m VProp
evalProp' env = evalProp (envToPropEnv env)

propClosure :: MonadEvaluator m => Env VProp -> Term Ix -> m (PropClosure n)
propClosure env t = pure (Closure env t)

propClosure' :: MonadEvaluator m => Env ValProp -> Term Ix -> m (PropClosure n)
propClosure' env = propClosure (envToPropEnv env)

envToPropEnv :: Env ValProp -> Env VProp
envToPropEnv = map (second prop)

spineToVProp :: forall m. MonadEvaluator m => VProp -> VSpine -> m VProp
spineToVProp base [] = pure base
spineToVProp base (sp :> VApp v) = do
  sp <- spineToVProp base sp
  v <- valToVProp v
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

valToVProp :: forall m. MonadEvaluator m => Val -> m VProp
valToVProp (VNeutral ne sp) = do
  ne <- valToVProp ne
  spineToVProp ne sp
valToVProp (VRigid x) = pure (PVar x)
valToVProp (VFlex mv env) = pure (PMeta mv (envToPropEnv env))
valToVProp (VU s) = pure (PU s)
valToVProp (VLambda x t) = PLambda x <$> closureToVProp t
valToVProp (VPi s x a b) = PPi s x <$> valToVProp a <*> closureToVProp b
valToVProp VZero = pure PZero
valToVProp (VSucc n) = PSucc <$> valToVProp n
valToVProp VNat = pure PNat
valToVProp (VExists x a b) = PExists x <$> valToVProp a <*> closureToVProp b
valToVProp (VAbort a t) = PAbort <$> valToVProp a <*> pure t
valToVProp VEmpty = pure PEmpty
valToVProp (VProp p) = pure p
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
valToVProp (VFixedPoint i g v f p x c t a) = do
  i <- valToVProp i
  c <- closureToVProp c
  t <- closureToVProp t
  a <- mapM valToVProp a
  let fp = PFixedPoint i g v f p x c t
  case a of
    Just a -> pure (PApp fp a)
    Nothing -> pure fp
valToVProp (VMu tag f t x cs functor a) = do
  t <- valToVProp t
  cs <- mapM consToVProp cs
  functor <- mapM vFunctorToPFunctor functor
  a <- mapM valToVProp a
  let muF = PMu tag f t x cs functor
  case a of
    Just a -> pure (PApp muF a)
    Nothing -> pure muF
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

closureToVProp :: forall m n. MonadEvaluator m => ValClosure n -> m (PropClosure n)
closureToVProp (Closure env t) = pure (Closure (map (second prop) env) t)
closureToVProp (Lift v) = Lift <$> valToVProp v
closureToVProp (LiftClosure cl) = LiftClosure <$> closureToVProp cl
closureToVProp (Function f) = do
  let f' = closureToVProp . f . embedProp
  Function <$> evaluate (push f')

appProp :: MonadEvaluator m => ClosureApply m n cl VProp VProp => Closure n VProp VProp -> cl
appProp = app evalProp

quoteProp :: forall m. MonadEvaluator m => Lvl -> VProp -> m (Term Ix)
quoteProp lvl (PVar x) = pure (Var (lvl2ix lvl x))
quoteProp _ (PMeta mv _) = pure (Meta mv)
quoteProp _ (PU s) = pure (U s)
quoteProp lvl (PLambda x t) = Lambda x <$> (quoteProp (lvl + 1) =<< appProp t (PVar lvl))
quoteProp lvl (PApp t u) = App <$> quoteProp lvl t <*> quoteProp lvl u
quoteProp lvl (PPi s x a b) = Pi s x <$> quoteProp lvl a <*> (quoteProp (lvl + 1) =<< appProp b (PVar lvl))
quoteProp _ PZero = pure Zero
quoteProp lvl (PSucc n) = Succ <$> quoteProp lvl n
quoteProp lvl (PNElim z a t0 x ih ts n) = do
  a <- quoteProp (lvl + 1) =<< appProp a (PVar lvl)
  t0 <- quoteProp lvl t0
  ts <- quoteProp (lvl + 2) =<< appProp ts (PVar lvl) (PVar (lvl + 1))
  n <- quoteProp lvl n
  pure (NElim z a t0 x ih ts n)
quoteProp _ PNat = pure Nat
quoteProp lvl (PPropPair t u) = PropPair <$> quoteProp lvl t <*> quoteProp lvl u
quoteProp lvl (PPropFst t) = PropFst <$> quoteProp lvl t
quoteProp lvl (PPropSnd t) = PropSnd <$> quoteProp lvl t
quoteProp lvl (PExists x a b) = Exists x <$> quoteProp lvl a <*> (quoteProp (lvl + 1) =<< appProp b (PVar lvl))
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
  t <- quoteProp (lvl + 1) =<< appProp t (PVar lvl)
  u <- quoteProp lvl u
  v <- quoteProp lvl v
  e <- quoteProp lvl e
  pure (Ap b x t u v e)
quoteProp lvl (PTransp t x pf b u t' e) = do
  t <- quoteProp lvl t
  b <- quoteProp (lvl + 2) =<< appProp b (PVar lvl) (PVar (lvl + 1))
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
quoteProp lvl (PSigma x a b) = Sigma x <$> quoteProp lvl a <*> (quoteProp (lvl + 1) =<< appProp b (PVar lvl))
quoteProp lvl (PQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) = do
  a <- quoteProp lvl a
  r <- quoteProp (lvl + 2) =<< appProp r (PVar lvl) (PVar (lvl + 1))
  rr <- quoteProp (lvl + 1) =<< appProp rr (PVar lvl)
  rs <- quoteProp (lvl + 3) =<< appProp rs (PVar lvl) (PVar (lvl + 1)) (PVar (lvl + 2))
  rt <- quoteProp (lvl + 5) =<< appProp rt (PVar lvl) (PVar (lvl + 1)) (PVar (lvl + 2)) (PVar (lvl + 3)) (PVar (lvl + 4))
  pure (Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)
quoteProp lvl (PQProj t) = QProj <$> quoteProp lvl t
quoteProp lvl (PQElim z b x tpi px py pe p u) = do
  b <- quoteProp (lvl + 1) =<< appProp b (PVar lvl)
  tpi <- quoteProp (lvl + 1) =<< appProp tpi (PVar lvl)
  p <- quoteProp (lvl + 3) =<< appProp p (PVar lvl) (PVar (lvl + 1)) (PVar (lvl + 2))
  u <- quoteProp lvl u
  pure (QElim z b x tpi px py pe p u)
quoteProp lvl (PIdRefl t) = IdRefl <$> quoteProp lvl t
quoteProp lvl (PIdPath e) = IdPath <$> quoteProp lvl e
quoteProp lvl (PJ a t x pf b u v e) = do
  a <- quoteProp lvl a
  t <- quoteProp lvl t
  b <- quoteProp (lvl + 2) =<< appProp b (PVar lvl) (PVar (lvl + 1))
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
quoteProp lvl (PFmap f a b g p x) = do
  f <- quoteProp lvl f
  a <- quoteProp lvl a
  b <- quoteProp lvl b
  g <- quoteProp lvl g
  p <- quoteProp lvl p
  x <- quoteProp lvl x
  pure (Fmap f a b g p x)
quoteProp lvl (PMatch t x p bs) = do
  t <- quoteProp lvl t
  p <- quoteProp (lvl + 1) =<< appProp p (PVar lvl)
  bs <- mapM quoteBranch bs
  pure (Match t x p bs)
  where
    quoteBranch
      :: (Name, Binder, Binder, PropClosure (A 2))
      -> m (Name, Binder, Binder, Term Ix)
    quoteBranch (c, x, e, t) = (c,x,e,) <$> (quoteProp (lvl + 2) =<< appProp t (PVar lvl) (PVar (lvl + 1)))
quoteProp lvl (PFixedPoint i g v f p x c t) = do
  i <- quoteProp lvl i
  c <- quoteProp (lvl + 4) =<< appProp c (PVar lvl) (PVar (lvl + 1)) (PVar (lvl + 2)) (PVar (lvl + 3))
  t <- quoteProp (lvl + 5) =<< appProp t (PVar lvl) (PVar (lvl + 1)) (PVar (lvl + 2)) (PVar (lvl + 3)) (PVar (lvl + 4))
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
      bi <- quoteProp (lvl + 2) =<< appProp bi (PVar lvl) (PVar (lvl + 1))
      ixi <- quoteProp (lvl + 3) =<< appProp ixi (PVar lvl) (PVar (lvl + 1)) (PVar (lvl + 2))
      pure (ci, si, xi, bi, f, ixi)

    quoteFunctor :: PFunctorInstance -> m (FunctorInstance Ix)
    quoteFunctor (PFunctorInstance a b f p x t) = do
      t <- quoteProp (lvl + 5) =<< appProp t (PVar lvl) (PVar (lvl + 1)) (PVar (lvl + 2)) (PVar (lvl + 3)) (PVar (lvl + 4))
      pure (FunctorInstanceF a b f p x t)
quoteProp lvl (PLet x a t u) = do
  a <- quoteProp lvl a
  t <- quoteProp lvl t
  u <- quoteProp (lvl + 1) =<< appProp u (PVar lvl)
  pure (Let x a t u)
quoteProp lvl (PAnnotation t a) = Annotation <$> quoteProp lvl t <*> quoteProp lvl a
