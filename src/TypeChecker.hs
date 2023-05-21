{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module TypeChecker (
  Checker (..),
  CheckState,
  emptyCheckState,
  infer,
  check,
  emptyContext,
) where

import Context
import Conversion
import Error
import Eval
import EvalProp
import MonadChecker
import PrettyPrinter
import Syntax
import Value

import Control.Lens hiding (Context, Empty, Refl, (:>))
import Control.Monad.Except
import Control.Monad.Oops

import Data.HashMap.Strict qualified as M
import Error.Diagnose

ppVal :: MonadEvaluator m => Context -> Val -> m TermString
ppVal gamma v = TS . prettyPrintTerm (names gamma) <$> quote (lvl gamma) v

checkSortKnown :: Relevance -> Checker (Variant e) Sort
checkSortKnown Relevant = pure Relevant
checkSortKnown Irrelevant = pure Irrelevant
checkSortKnown (SortMeta m) = do
  s <- lookupSortMeta m
  case s of
    Nothing -> error "TODO: error"
    Just s -> checkSortKnown s

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
  -> Checker (Variant e) (Term Ix, VTy, Relevance)
inferVar pos types name = do
  (i, ty, s) <- find types name
  pure (Var i, ty, s)
  where
    find :: Types -> Name -> Checker (Variant e) (Ix, VTy, Relevance)
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
     )
  => Context
  -> Raw
  -> Checker (Variant e) (Term Ix, VTy, Relevance)
infer gamma (R pos (VarF x)) = inferVar pos (types gamma) x
infer _ (R _ (UF s)) = do
  s <- checkSort s
  pure (U s, VU Relevant, Relevant)
infer gamma (R _ (AppF _ t@(R fnPos _) u)) = do
  (t, tty, s) <- infer gamma t
  (s', a, b) <- case tty of
    VPi s' _ a b -> pure (s', a, b)
    -- VMeta {} -> do
    --   -- If the type is a metavariable, then construct a fresh Pi type with metas
    --   -- for each position, and solve the constraint ?α ≡ Π(x : ?β). ?γ
    --   -- TODO: add more rules like this
    --   s' <- SortMeta <$> freshSortMeta
    --   a <- Meta <$> freshMeta (names gamma)
    --   b <- Meta <$> freshMeta (names gamma)
    --   va <- eval (env gamma) a
    --   let vb vx = eval (env gamma :> (Bound, vx)) b
    --   vb <- makeFnClosure' vb
    --   conv fnPos (names gamma) (lvl gamma) tty (VPi s' Hole va vb)
    --   pure (s', va, vb)
    _ -> do
      tTS <- ppVal gamma tty
      throw (ApplicationHead tTS fnPos)
  u <- check gamma u a
  s' <- checkSortKnown s'
  vu <- eval' s' (env gamma) u
  b_u <- app b vu
  pure (App s' t u, b_u, s)
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
  vzero <- embedVal VZero
  a0 <- eval (env gamma :> (Bound, vzero)) a
  t0 <- check gamma t0 a0
  let xVar = VVar (lvl gamma)
  vx <- embedVal xVar
  ax <- eval (env gamma :> (Bound, vx)) a
  vSx <- embedVal (VSucc xVar)
  aSx <- eval (env gamma :> (Bound, vSx)) a
  ts <- check (gamma & bindR x VNat & bind ih s ax) ts aSx
  -- In general, argument to inductor should be inferred, but can be checked
  -- in simple case of Nat
  n <- check gamma n VNat
  vn_val <- eval (env gamma) n
  vn <- embedVal vn_val
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
      t_prop <- evalProp (env gamma) t
      b_fst_t <- app b (Prop (PPropFst t_prop))
      pure (PropSnd t, b_fst_t, Irrelevant)
    VSigma _ _ b -> do
      vt <- eval (env gamma) t
      fst_vt <- vt $$ VFst >>= embedVal
      b_fst_t <- app b fst_vt
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
  convSort pos s Relevant
  vt <- eval (env gamma) t
  vt_eq_vt <- eqReduce vt a vt
  pure (Refl t, vt_eq_vt, Irrelevant)
infer gamma (R _ (SymF t@(R pos _) u e)) = do
  (t, a, s) <- infer gamma t
  -- aTS <- ppVal gamma a
  -- when (s == Irrelevant) (throw (SymmetryIrrelevant aTS pos))
  convSort pos s Relevant
  u <- check gamma u a
  vt <- eval (env gamma) t
  vu <- eval (env gamma) u
  vt_eq_vu <- eqReduce vt a vu
  e <- check gamma e vt_eq_vu
  vu_eq_vt <- eqReduce vu a vt
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
  vt_eq_vu <- eqReduce vt a vu
  e <- check gamma e vt_eq_vu
  vu_eq_vv <- eqReduce vu a vv
  e' <- check gamma e' vu_eq_vv
  vt_eq_vv <- eqReduce vt a vv
  pure (Trans t u v e e', vt_eq_vv, Irrelevant)
infer gamma (R _ (ApF b x t u@(R pos _) v e)) = do
  (u, a, s) <- infer gamma u
  -- aTS <- ppVal gamma a
  -- when (s == Irrelevant) (throw (CongruenceDomainIrrelevant aTS pos))
  convSort pos s Relevant
  v <- check gamma v a
  vu_val <- eval (env gamma) u
  vu <- embedVal vu_val
  vv_val <- eval (env gamma) v
  vv <- embedVal vv_val
  vu_eq_vv <- eqReduce vu_val a vv_val
  e <- check gamma e vu_eq_vv
  b <- check gamma b (VU Relevant)
  vb <- eval (env gamma) b
  t <- check (gamma & bindR x a) t vb
  vt_u <- eval (env gamma :> (Bound, vu)) t
  vt_v <- eval (env gamma :> (Bound, vv)) t
  vt_u_eq_vt_v <- eqReduce vt_u vb vt_v
  pure (Ap b x t u v e, vt_u_eq_vt_v, Irrelevant)
infer gamma (R _ (TranspF t@(R pos _) x pf b u t' e)) = do
  (t, va, s) <- infer gamma t
  convSort pos s Relevant
  t' <- check gamma t' va
  vt_val <- eval (env gamma) t
  vt <- embedVal vt_val
  vt'_val <- eval (env gamma) t'
  vt' <- embedVal vt'_val
  let vx = VVar (lvl gamma)
  t_eq_x <- eqReduce vt_val va vx
  b <- check (gamma & bindR x va & bindP pf t_eq_x) b (VU Irrelevant)
  let refl_t = Prop (PRefl (prop vt))
  b_t_refl <- eval (env gamma :> (Bound, vt) :> (Bound, refl_t)) b
  u <- check gamma u b_t_refl
  vt_eq_vt' <- eqReduce vt_val va vt'_val
  e <- check gamma e vt_eq_vt'
  e_prop <- evalProp (env gamma) e
  b_t'_e <- eval (env gamma :> (Bound, vt') :> (Bound, Prop e_prop)) b
  pure (Transp t x pf b u t' e, b_t'_e, Irrelevant)
infer gamma (R _ (CastF a@(R aPos _) b@(R bPos _) e t)) = do
  (a, s) <- checkType gamma a
  (b, s') <- checkType gamma b
  va <- eval (env gamma) a
  vb <- eval (env gamma) b
  when (s /= s') (throw (CastBetweenUniverses s aPos s' bPos))
  va_eq_vb <- eqReduce va (VU s) vb
  e <- check gamma e va_eq_vb
  t <- check gamma t va
  pure (Cast a b e t, vb, s)
infer gamma (R _ (SigmaF x a b)) = do
  a <- check gamma a (VU Relevant)
  va <- eval (env gamma) a
  b <- check (bindR x va gamma) b (VU Relevant)
  pure (Sigma x a b, VU Relevant, Relevant)
infer gamma (R _ (QuotientF a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)) = do
  a <- check gamma a (VU Relevant)
  va <- eval (env gamma) a
  r <- check (gamma & bindR x va & bindR y va) r (VU Irrelevant)
  let vx = varR (lvl gamma)
      vy = varR (lvl gamma + 1)
      vz = varR (lvl gamma + 2)
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
    VQuotient a _ _ r _ _ _ _ _ rs _ _ _ _ _ _ -> do
      (b, s) <- checkType (gamma & bindR z uty) b
      let xVar = VVar (lvl gamma)
          yVar = VVar (lvl gamma + 1)
          ve = varP (lvl gamma + 2)
      vx <- embedVal xVar
      vy <- embedVal yVar
      vproj_x <- embedVal (VQProj xVar)
      vproj_y <- embedVal (VQProj yVar)
      b_pix <- eval (env gamma :> (Bound, vproj_x)) b
      b_piy <- eval (env gamma :> (Bound, vproj_y)) b
      tpi <- check (gamma & bindR x a) tpi b_pix
      tpi_x <- eval (env gamma :> (Bound, vx)) tpi
      tpi_y <- eval (env gamma :> (Bound, vy)) tpi

      e_inv_prop <- app rs (restrict vx) (restrict vy) (restrict ve)

      tpi_x_prop <- freeze tpi_x
      tpi_y_prop <- freeze tpi_y

      b_prop <- propClosure (env gamma) b

      let ap_B_e_inv = PAp (PU s) z b_prop tpi_x_prop tpi_y_prop e_inv_prop

      cast_b_piy_b_pix <- cast b_piy b_pix ap_B_e_inv tpi_y
      tpi_x_eq_tpi_y <- eqReduce tpi_x b_pix cast_b_piy_b_pix

      r_x_y <- app r vx vy
      let gamma''' = gamma & bindR px a & bindR py a & bindP pe r_x_y
      p <- check gamma''' p tpi_x_eq_tpi_y
      vu_val <- eval (env gamma) u
      vu <- embedVal vu_val
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
  vt_val <- eval (env gamma) t
  vt <- embedVal vt_val
  let vx = VVar (lvl gamma)
  (b, s) <- checkType (gamma & bindR x va & bindR pf (VId va vt_val vx)) b
  vidrefl_t <- embedVal (VIdRefl vt_val)
  b_t_idrefl_t <- eval (env gamma :> (Bound, vt) :> (Bound, vidrefl_t)) b
  u <- check gamma u b_t_idrefl_t
  t' <- check gamma t' va
  vt'_val <- eval (env gamma) t'
  vt' <- embedVal vt'_val
  e <- check gamma e (VId va vt_val vt'_val)
  ve_val <- eval (env gamma) e
  ve <- embedVal ve_val
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
infer _ (R _ RUnitF) = pure (RUnit, VU Relevant, Relevant)
infer _ (R _ ROneF) = pure (ROne, VRUnit, Relevant)
infer gamma (R _ (FLiftF f@(R pos _) a)) = do
  (f, fty, s) <- infer gamma f
  vf <- eval (env gamma) f
  -- Lifting is only valid if the argument is an inductive type
  case vf of
    VMu {} -> do
      a <- check gamma a fty
      pure (FLift f a, fty, s)
    _ -> do
      fTS <- ppVal gamma vf
      throw (FLiftNotInductiveType fTS pos)
infer gamma (R _ (FmapF f@(R pos _) a b g p x)) = do
  (f, _, _) <- infer gamma f
  vf <- eval (env gamma) f
  case vf of
    VMu _ f' pty cs functor@(Just (VFunctorInstance _ _ _ _ x' _)) Nothing -> do
      let fty = VPi Relevant Hole pty (Lift (VU Relevant))
      a <- check gamma a fty
      (va_entry, va) <- eval (env gamma) a >>= embedVal'
      b <- check gamma b fty
      (vb_entry, vb) <- eval (env gamma) b >>= embedVal'
      let gty = VPi Relevant x' pty (Defun (ClosureNaturalTransformation va vb))
      g <- check gamma g gty
      p <- check gamma p pty
      vp <- eval (env gamma) p
      f_lift_a_tag <- freshTag
      let f_lift_a = functorLift f_lift_a_tag f' pty cs functor va_entry
      f_lift_a_p <- f_lift_a $$ VApp vp
      x <- check gamma x f_lift_a_p
      f_lift_b_tag <- freshTag
      let f_lift_b = functorLift f_lift_b_tag f' pty cs functor vb_entry
      f_lift_b_p <- f_lift_b $$ VApp vp
      pure (Fmap f a b g p x, f_lift_b_p, Relevant)
    _ -> throw (FmapNeedsFunctorInstance pos)
infer gamma (R pos (MatchF t@(R argPos _) x c bs)) = do
  (t, a, _) <- infer gamma t
  case a of
    -- We must have [Just a], otherwise this is not a type.
    VMu tag f aty constructors functor (Just a) -> do
      let pVar = VVar (lvl gamma)
          vmuF_p = VMu tag f aty constructors functor (Just pVar)
      (c, s) <- checkType (gamma & bindR x vmuF_p) c

      let muF_val = VMu tag f aty constructors functor Nothing
      muF <- embedVal muF_val
      let
        -- checkBranches returns a set of remaining constructors.
        -- Each step we check if the constructor is in the remaining set,
        -- and then remove it. This allows us to check for totality.
        checkBranches [] = pure ([], M.fromList constructors)
        checkBranches (brs :> (ci, xi, ei, ti)) = do
          (brs, cs) <- checkBranches brs
          case M.lookup ci cs of
            Nothing -> do
              muFTS <- ppVal gamma muF_val
              throw (ConstructorNotInTypeMatch ci muFTS pos)
            Just (_, bi, ixi) -> do
              b_muF_a <- app bi muF
              let xVar = VVar (lvl gamma)
                  eVar = PVar (lvl gamma + 1)

              vx <- embedVal xVar
              ixi_muF_a_x <- app ixi muF vx

              ixi_eq_a <- eqReduce ixi_muF_a_x aty a

              let gamma'' = gamma & bindR xi b_muF_a & bindP ei ixi_eq_a

              vCx <- embedVal (VCons ci xVar eVar)
              cCx <- eval (env gamma :> (Bound, vCx)) c
              ti <- check gamma'' ti cCx

              pure (brs :> (ci, xi, ei, ti), M.delete ci cs)

      (bs, remaining) <- checkBranches bs
      unless (M.null remaining) (throw (NonTotalMatch (M.keys remaining) pos))
      vt_val <- eval (env gamma) t
      vt <- embedVal vt_val
      vc_t <- eval (env gamma :> (Bound, vt)) c
      pure (Match t x c bs, vc_t, s)
    a -> do
      aTS <- ppVal gamma a
      throw (MatchHead aTS argPos)
infer gamma (R _ (FixedPointF i@(R pos _) g v f p x c t)) = do
  (muF, _, _) <- infer gamma i
  vmuF <- eval (env gamma) muF
  case vmuF of
    VMu _ f' a cs functor Nothing -> do
      let vmuFty = VPi Relevant Hole a (Lift (VU Relevant))
      let gVar = VVar (lvl gamma)
          vVar = VVar (lvl gamma + 1)
          pVar = VVar (lvl gamma + 2)
      let viewTy = buildViewType a gVar vmuF
      vg_p <- gVar $$ VApp pVar
      let gammaC = gamma & bindR g vmuFty & bindR v viewTy & bindR p a & bindR x vg_p
      (c, s) <- checkType gammaC c

      vg <- embedVal gVar
      vv <- embedVal vVar
      let fty = buildFType p a (env gamma) vg vv c

      f_lift_g_tag <- freshTag
      let pVar = VVar (lvl gamma + 3)
          f_lift_g_val = functorLift f_lift_g_tag f' a cs functor vg
      f_lift_g <- embedVal f_lift_g_val
      f_lift_g_p <- f_lift_g_val $$ VApp pVar
      vmuF <- embedVal vmuF
      vv_lifted_val <- liftView v functor vg vmuF vv
      vv_lifted <- embedVal vv_lifted_val
      vp <- embedVal pVar
      let vx = varR (lvl gamma + 4)
      c_f_lift_g_v_p_x <- eval (env gamma :> (Bound, f_lift_g) :> (Bound, vv_lifted) :> (Bound, vp) :> (Bound, vx)) c
      let gammaT = gamma & bindR g vmuFty & bindR v viewTy & bind f s fty & bind p s a & bindR x f_lift_g_p
      t <- check gammaT t c_f_lift_g_v_p_x

      viewId_val <- valIdentity x
      viewId <- embedVal viewId_val

      let fixTy = buildFType p a (env gamma) vmuF viewId c
      pure (FixedPoint muF g v f p x c t, fixTy, s)
    _ -> do
      vmuFTS <- ppVal gamma vmuF
      throw (FixAnnotation vmuFTS pos)
  where
    buildFType :: Binder -> VTy -> Env -> EnvEntry -> EnvEntry -> Term Ix -> VTy
    buildFType p a env vg vv c = do
      let env' = env :> (Bound, vg) :> (Bound, vv)
       in VPi Relevant p a (Defun (ClosureFixFType x (val vg) env' c))

    buildViewType :: VTy -> VTy -> VTy -> VTy
    buildViewType a g muF = VPi Relevant p a (Defun (ClosureNaturalTransformation g muF))

    liftView :: Binder -> Maybe VFunctorInstance -> EnvEntry -> EnvEntry -> EnvEntry -> Checker (Variant e) Val
    -- This is a hack -- it says if the view is not used (not given a name), then we don't lift it
    -- in a well-typed manner. This allows fixed points over inductive types without an explicit
    -- functor definition provided they don't use views.
    -- TODO: Infer functor definitions when not explicitly provided to avoid this hack
    liftView Hole _ _ _ view = pure (val view)
    liftView _ (Just (VFunctorInstance _ _ _ _ _ t)) vg vmuF view =
      -- Lifts ι : (p : X) → G p → μF p
      -- to F[ι] : (p : X) → F[G] p → F[μF] p
      -- and then applies the isomorphism F[μF] p ≅ μF p
      pure (VLambda Relevant p (Defun (ClosureLiftView x t vmuF vg view)))
    liftView _ _ _ _ _ = throw (FixViewWithNoFunctor pos)
infer gamma (R muPos (MuF () f a cs functor)) = do
  a <- check gamma a (VU Relevant)
  va <- eval (env gamma) a
  let vfty = VPi Relevant Hole va (Lift (VU Relevant))
  let gamma' = gamma & bindR (Name f) vfty
  cs <- mapM (checkConstructor gamma' va) cs
  -- A fresh tag is associated to each syntactic inductive type definition.
  tag <- freshTag
  vcs <- mapM evalConstructor cs
  let vmuF_val = VMu tag f va vcs Nothing Nothing
  vmuF <- embedVal vmuF_val
  -- Functor action on objects (which are themselves functors)
  let f_lift ty = do
        f_lift_ty_tag <- freshTag
        pure (functorLift f_lift_ty_tag f va vcs Nothing ty)
  -- Check the provided functor action on morphisms (which are natural transformations)
  functor <- mapM (checkFunctor vmuF va f_lift) functor
  pure (Mu tag f a cs functor, vfty, Relevant)
  where
    checkConstructor
      :: Context
      -> VTy
      -> (Name, Binder, Raw, Name, Raw)
      -> Checker (Variant e) (Name, Binder, Type Ix, Name, Type Ix)
    checkConstructor gamma' ixTy (ci, xi, bi, fi, ix)
      | f == fi = do
          bi <- check gamma' bi (VU Relevant)
          vbi <- eval (env gamma') bi
          ix <- check (gamma' & bindR xi vbi) ix ixTy
          pure (ci, xi, bi, f, ix)
      | otherwise = throw (InductiveTypeConstructor f fi muPos)

    evalConstructor
      :: (Name, Binder, Term Ix, Name, Term Ix)
      -> Checker (Variant e) (Name, (Binder, ValClosure (A 1), ValClosure (A 2)))
    evalConstructor (ci, xi, bi, _, ixi) = do
      bi <- closure (env gamma) bi
      ixi <- closure (env gamma) ixi
      pure (ci, (xi, bi, ixi))

    checkFunctor
      :: EnvEntry
      -> VTy
      -> (EnvEntry -> Checker (Variant e) VTy)
      -> FunctorInstanceF Raw
      -> Checker (Variant e) (FunctorInstance Ix)
    checkFunctor vmuF argTy f_lift (FunctorInstanceF a b nt p x' t) = do
      let aVar = VVar (lvl gamma + 1)
          bVar = VVar (lvl gamma + 2)
      va <- embedVal aVar
      vb <- embedVal bVar
      f_lift_a <- f_lift va
      f_lift_b <- f_lift vb
      let ntTy = VPi Relevant p argTy (Defun (ClosureNaturalTransformation aVar bVar))
      let vp = VVar (lvl gamma + 4)
      f_lift_a_p <- f_lift_a $$ VApp vp
      f_lift_b_p <- f_lift_b $$ VApp vp
      let famTy = VPi Relevant Hole argTy (Lift (VU Relevant))
      let gamma' =
            gamma
              & define (Name f) vmuF Relevant famTy
              & bindR a famTy
              & bindR b famTy
              & bindR nt ntTy
              & bindR p argTy
              & bindR x' f_lift_a_p
      t <- check gamma' t f_lift_b_p
      pure (FunctorInstanceF a b nt p x' t)
infer gamma (R _ (LetF x () a t u)) = do
  (a, s) <- checkType gamma a
  va <- eval (env gamma) a
  t <- check gamma t va
  s_known <- checkSortKnown s
  vt <- eval' s_known (env gamma) t
  (u, uty, s') <- infer (define x vt s va gamma) u
  pure (Let x s_known a t u, uty, s')
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
infer gamma (R pos (GoalF () terms)) = do
  termsTS <- forM terms $ \((), t) -> do
    (t, a, _) <- infer gamma t
    let tTS = TS (prettyPrintTerm (names gamma) t)
    aTS <- ppVal gamma a
    pure (tTS, aTS)
  throw (InferGoal termsTS pos)
infer _ (R pos _) = throw (InferenceFailure pos)

checkType
  :: ( e `CouldBe` CheckError
     , e `CouldBe` InferenceError
     , e `CouldBe` ConversionError
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

check
  :: forall e
   . ( e `CouldBe` CheckError
     , e `CouldBe` InferenceError
     , e `CouldBe` ConversionError
     )
  => Context
  -> Raw
  -> VTy
  -> Checker (Variant e) (Term Ix)
check gamma (R _ (LambdaF () x t)) (VPi s _ a b) = do
  s' <- checkSortKnown s
  b' <- app b (var s' (lvl gamma))
  t <- check (bind x s a gamma) t b'
  pure (Lambda s' x t)
check gamma (R pos (LambdaF {})) tty = do
  tTS <- ppVal gamma tty
  throw (CheckLambda tTS pos)
check gamma (R _ (PropPairF t u)) (VExists _ a b) = do
  t <- check gamma t a
  t_prop <- evalProp (env gamma) t
  b_t <- app b (Prop t_prop)
  u <- check gamma u b_t
  pure (PropPair t u)
check gamma (R pos (PropPairF {})) tty = do
  tTS <- ppVal gamma tty
  throw (CheckPropPair tTS pos)
check gamma (R _ (PairF t u)) (VSigma _ a b) = do
  t <- check gamma t a
  vt_val <- eval (env gamma) t
  vt <- embedVal vt_val
  b_t <- app b vt
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
  t_eq_u <- eqReduce t a u
  e <- check gamma e t_eq_u
  pure (IdPath e)
check gamma (R pos (IdPathF {})) tty = do
  tTS <- ppVal gamma tty
  throw (CheckIdPath tTS pos)
check gamma (R pos (ConsF c t e)) (VMu tag f aty cs functor (Just a)) = do
  let muF = VMu tag f aty cs functor Nothing
  case lookup c cs of
    Nothing -> do
      muFTS <- ppVal gamma muF
      throw (ConstructorNotInTypeCons c muFTS pos)
    Just (_, bi, ixi) -> do
      muF <- embedVal muF
      -- Apply [bi] to inductive type without parameters
      bi_muF_a <- app bi muF
      t <- check gamma t bi_muF_a
      vt_val <- eval (env gamma) t
      vt <- embedVal vt_val
      ixi_muF_a_x <- app ixi muF vt
      ixi_eq_a <- eqReduce ixi_muF_a_x aty a
      e <- check gamma e ixi_eq_a
      pure (Cons c t e)
check gamma (R pos (ConsF c _ _)) tty = do
  tTS <- ppVal gamma tty
  throw (CheckCons tTS c pos)
check gamma (R _ (InF t)) (VMu tag f aty cs functor (Just a)) = do
  let muF_val = VMu tag f aty cs functor Nothing
  muF <- embedVal muF_val
  let f_lift_muF = functorLift tag f aty cs functor muF
  f_lift_muF_a <- f_lift_muF $$ VApp a
  check gamma t f_lift_muF_a
check gamma (R pos (InF _)) tty = do
  tTS <- ppVal gamma tty
  throw (CheckIn tTS pos)
check gamma (R _ (BoxProofF e)) (VBox a) = do
  e <- check gamma e a
  pure (BoxProof e)
check gamma (R pos (BoxProofF {})) tty = do
  tTS <- ppVal gamma tty
  throw (CheckBoxProof tTS pos)
check gamma (R _ (LetF x () a t u)) uty = do
  (a, s) <- checkType gamma a
  va <- eval (env gamma) a
  t <- check gamma t va
  s' <- checkSortKnown s
  vt <- eval' s' (env gamma) t
  u <- check (define x vt s va gamma) u uty
  pure (Let x s' a t u)
check gamma (R pos (GoalF () terms)) goal = do
  goalTS <- ppVal gamma goal
  termsTS <- forM terms $ \((), t) -> do
    (t, a, _) <- infer gamma t
    let tTS = TS (prettyPrintTerm (names gamma) t)
    aTS <- ppVal gamma a
    pure (tTS, aTS)
  throw (CheckGoal goalTS termsTS pos)
check gamma t@(R pos _) tty = do
  (t, tty', _) <- infer gamma t
  conv pos (names gamma) (lvl gamma) tty tty'
  pure t
