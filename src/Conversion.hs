{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Conversion (
  conv,
  convSort,
)
where

import Error
import Eval
import MonadChecker
import PatternUnification
import PrettyPrinter
import Syntax
import Value

import Control.Monad.Except
import Control.Monad.Oops
import Data.Function ((&))
import Data.Void
import Error.Diagnose

convSort
  :: e `CouldBe` ConversionError
  => Position
  -> Relevance
  -> Relevance
  -> Checker (Variant e) ()
convSort pos s s' = do
  Checker
    ( catch @ErrorDuringConversion
        (throw . ErrorDuringConversion (TS (show s)) (TS (show s')))
        (runChecker (convSort' pos s s'))
    )

convSort'
  :: e `CouldBe` ErrorDuringConversion
  => Position
  -> Relevance
  -> Relevance
  -> Checker (Variant e) ()
convSort' _ Relevant Relevant = pure ()
convSort' _ Irrelevant Irrelevant = pure ()
convSort' pos Relevant Irrelevant = throw (ConversionBetweenUniverses pos)
convSort' pos Irrelevant Relevant = throw (ConversionBetweenUniverses pos)
-- TODO: occurs check for sort metas (?)
convSort' _ (SortMeta m) s = addSortSolution m s
convSort' _ s (SortMeta m) = addSortSolution m s

conv
  :: ( e `CouldBe` ConversionError
     )
  => Position
  -> [Binder]
  -> Lvl
  -> Val
  -> Val
  -> Checker (Variant e) ()
conv pos names lvl a b = do
  aTS <- TS . prettyPrintTerm names <$> quote lvl a
  bTS <- TS . prettyPrintTerm names <$> quote lvl b
  Checker
    ( runChecker (conv' names names lvl a b)
        & catch @ErrorDuringConversion (throw . ErrorDuringConversion aTS bTS)
        & catch @ErrorDuringUnification (throw . ErrorDuringUnification aTS bTS)
    )
  where
    convSp
      :: forall e
       . (e `CouldBe` ErrorDuringConversion, e `CouldBe` ErrorDuringUnification)
      => [Binder]
      -> [Binder]
      -> Lvl
      -> VSpine
      -> VSpine
      -> Checker (Variant e) ()
    convSp _ _ _ [] [] = pure ()
    convSp ns ns' lvl (sp :> VApp u) (sp' :> VApp u') = do
      convSp ns ns' lvl sp sp'
      conv' ns ns' lvl u u'
    convSp ns ns' lvl (sp :> VAppProp _) (sp' :> VAppProp _) = do
      convSp ns ns' lvl sp sp'
    convSp ns ns' lvl (sp :> VNElim z a t0 x ih ts) (sp' :> VNElim z' a' t0' x' ih' ts') = do
      convSp ns ns' lvl sp sp'
      let vz = varR lvl
      a_z <- app a vz
      a'_z <- app a' vz
      conv' (ns :> z) (ns' :> z') (lvl + 1) a_z a'_z
      conv' ns ns' lvl t0 t0'
      let vx = varR lvl
          vih = varR (lvl + 1)
      ts_x_ih <- app ts vx vih
      ts'_x_ih <- app ts' vx vih
      conv' (ns :> x :> ih) (ns' :> x' :> ih') (lvl + 2) ts_x_ih ts'_x_ih
    convSp ns ns' lvl (sp :> VFst) (sp' :> VFst) = convSp ns ns' lvl sp sp'
    convSp ns ns' lvl (sp :> VSnd) (sp' :> VSnd) = convSp ns ns' lvl sp sp'
    convSp ns ns' lvl (sp :> VQElim z b x tpi _ _ _ _) (sp' :> VQElim z' b' x' tpi' _ _ _ _) = do
      convSp ns ns' lvl sp sp'
      let vz = varR lvl
      b_z <- app b vz
      b'_z <- app b' vz
      let vx = varR lvl
      tpi_x <- app tpi vx
      tpi'_x <- app tpi' vx
      conv' (ns :> z) (ns' :> z') (lvl + 1) b_z b'_z
      conv' (ns :> x) (ns' :> x') (lvl + 1) tpi_x tpi'_x
    convSp ns ns' lvl (sp :> VJ a t x pf b u v) (sp' :> VJ a' t' x' pf' b' u' v') = do
      convSp ns ns' lvl sp sp'
      conv' ns ns' lvl a a'
      conv' ns ns' lvl t t'
      let vx = varR lvl
          vpf = varR (lvl + 1)
      b_x_pf <- app b vx vpf
      b'_x_pf <- app b' vx vpf
      conv' (ns :> x :> pf) (ns' :> x' :> pf') (lvl + 2) b_x_pf b'_x_pf
      conv' ns ns' lvl u u'
      conv' ns ns' lvl v v'
    convSp ns ns' lvl (sp :> VBoxElim) (sp' :> VBoxElim) = convSp ns ns' lvl sp sp'
    convSp ns ns' lvl (sp :> VMatch x c bs) (sp' :> VMatch x' c' bs') = do
      convSp ns ns' lvl sp sp'
      let vx = varR (lvl + 1)
      c_x <- app c vx
      c'_x <- app c' vx
      conv' (ns :> x) (ns' :> x') (lvl + 1) c_x c'_x
      zipWithM_ convBranch bs bs'
      where
        -- TODO: don't assume same ordering
        convBranch
          :: (Name, Binder, Binder, ValClosure (A 2))
          -> (Name, Binder, Binder, ValClosure (A 2))
          -> Checker (Variant e) ()
        convBranch (c, x, e, t) (c', x', e', t')
          | c == c' = do
              let vx = varR lvl
                  ve = varR (lvl + 1)
              t <- app t vx ve
              t' <- app t' vx ve
              conv' (ns :> x :> e) (ns' :> x' :> e') (lvl + 2) t t'
          | otherwise = throw (ConstructorMismatch c c' pos)
    convSp _ _ _ sp sp' =
      throw (RigidSpineMismatch (TS . showElimHead <$> safeHead sp) (TS . showElimHead <$> safeHead sp') pos)
      where
        safeHead :: [a] -> Maybe a
        safeHead [] = Nothing
        safeHead (hd : _) = Just hd

    -- Conversion checking
    conv'
      :: forall e
       . (e `CouldBe` ErrorDuringConversion, e `CouldBe` ErrorDuringUnification)
      => [Binder]
      -> [Binder]
      -> Lvl
      -> Val
      -> Val
      -> Checker (Variant e) ()
    -- Flex conversion: attempt to unify
    conv' ns _ lvl (VNeutral (VFlex m env) sp) t = solve pos ns lvl m env sp t
    conv' _ ns lvl t (VNeutral (VFlex m env) sp) = solve pos ns lvl m env sp t
    conv' ns ns' lvl (VNeutral ne sp) (VNeutral ne' sp') = do
      convSp ns ns' lvl sp sp'
      conv' ns ns' lvl ne ne'
    -- Rigid-rigid conversion: heads must be equal and spines convertible
    conv' _ _ _ (VRigid x) (VRigid x')
      | x == x' = pure ()
    conv' _ _ _ (VU s) (VU s') = convSort' pos s s'
    conv' ns ns' lvl (VLambda s x t) (VLambda _ x' t') = do
      let vx = var s lvl
      t_x <- app t vx
      t'_x <- app t' vx
      conv' (ns :> x) (ns' :> x') (lvl + 1) t_x t'_x
    conv' ns ns' lvl (VLambda s x t) t' = do
      t_x <- app t (var s lvl)
      t'_x <- case s of
        Relevant -> t' $$ VApp (VVar lvl)
        Irrelevant -> t' $$ VAppProp (PVar lvl)
        SortMeta s -> absurd s
      conv' (ns :> x) (ns' :> x) (lvl + 1) t_x t'_x
    conv' ns ns' lvl t (VLambda s' x' t') = do
      t_x <- case s' of
        Relevant -> t $$ VApp (VVar lvl)
        Irrelevant -> t $$ VAppProp (PVar lvl)
        SortMeta s -> absurd s
      t'_x <- app t' (var s' lvl)
      conv' (ns :> x') (ns' :> x') (lvl + 1) t_x t'_x
    conv' ns ns' lvl (VPi s x a b) (VPi s' x' a' b') = do
      convSort' pos s s'
      conv' ns ns' lvl a a'
      let vx = varR lvl
      b_x <- app b vx
      b'_x <- app b' vx
      conv' (ns :> x) (ns' :> x') (lvl + 1) b_x b'_x
    conv' _ _ _ VZero VZero = pure ()
    conv' ns ns' lvl (VSucc n) (VSucc n') = conv' ns ns' lvl n n'
    conv' _ _ _ VNat VNat = pure ()
    conv' ns ns' lvl (VExists x a b) (VExists x' a' b') = do
      conv' ns ns' lvl a a'
      let vx = varR lvl
      b_x <- app b vx
      b'_x <- app b' vx
      conv' (ns :> x) (ns' :> x') (lvl + 1) b_x b'_x
    -- Both terms have the same type (by invariant), so [a ≡ a'], and [t] and [t'] are
    -- both of type [⊥], thus also convertible.
    conv' _ _ _ (VAbort {}) (VAbort {}) = pure ()
    conv' _ _ _ VEmpty VEmpty = pure ()
    conv' _ _ _ VUnit VUnit = pure ()
    conv' ns ns' lvl (VEq t a u) (VEq t' a' u') = do
      conv' ns ns' lvl t t'
      conv' ns ns' lvl a a'
      conv' ns ns' lvl u u'
    conv' ns ns' lvl cast@(VCast a b _ t) cast'@(VCast a' b' _ t') = do
      -- First try to compare [a ≡ b]. If success, compare [t ≡ cast(a', b', e', t')]
      -- Else, try to compare [a' ≡ b']. If success, compare [cast(a, b, e, t) ≡ t']
      -- Otherwise, compare casts structurally.
      tryChoice
        (conv' ns ns lvl a b)
        (conv' ns ns' lvl t cast')
        ( tryChoice
            (conv' ns' ns' lvl a' b')
            (conv' ns ns' lvl cast t')
            ( do
                conv' ns ns' lvl a a'
                conv' ns ns' lvl b b'
                -- [e ≡ e'] follows from proof irrelevance, given [a ≡ a'] and [b ≡ b']
                conv' ns ns' lvl t t'
            )
        )
    -- These rules implement definitional castrefl. Instead of a propositional
    -- constant [castrefl : cast(A, A, e, t) ~ t], we make this hold definitionally.
    -- Note that it does _not_ reduce in general, and is only handled in the conversion
    -- algorithm.
    conv' ns ns' lvl (VCast a b _ t) u = do
      conv' ns ns lvl a b
      conv' ns ns' lvl t u
    conv' ns ns' lvl t (VCast a b _ u) = do
      conv' ns' ns' lvl a b
      conv' ns ns' lvl t u
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
      let vx = varR lvl
      b_x <- app b vx
      b'_x <- app b' vx
      conv' (ns :> x) (ns' :> x') (lvl + 1) b_x b'_x
    conv' ns ns' lvl (VQuotient a x y r _ _ _ _ _ _ _ _ _ _ _ _) (VQuotient a' x' y' r' _ _ _ _ _ _ _ _ _ _ _ _) = do
      conv' ns ns' lvl a a'
      let vx = varR lvl
          vy = varR (lvl + 1)
      r_x_y <- app r vx vy
      r'_x_y <- app r' vx vy
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
    -- Partial eta law for unit type (expands one side, but can't convert on vars [Γ ⊢ x ≡ y : 1])
    conv' _ _ _ VROne _ = pure ()
    conv' _ _ _ _ VROne = pure ()
    conv' _ _ _ VRUnit VRUnit = pure ()
    conv' ns ns' lvl (VCons c t _) (VCons c' t' _)
      | c == c' = do
          conv' ns ns' lvl t t'
    conv' ns ns' lvl (VIn t) (VIn t') = conv' ns ns' lvl t t'
    conv' ns ns' lvl (VFLift f a) (VFLift f' a') = do
      conv' ns ns' lvl f f'
      conv' ns ns' lvl a a'
    conv' ns ns' lvl (VFmap f a b g p x) (VFmap f' a' b' g' p' x') = do
      conv' ns ns' lvl f f'
      conv' ns ns' lvl a a'
      conv' ns ns' lvl b b'
      conv' ns ns' lvl g g'
      conv' ns ns' lvl p p'
      conv' ns ns' lvl x x'
    conv' ns ns' lvl (VFixedPoint i g v f p x c t a) (VFixedPoint i' g' v' f' p' x' c' t' a') = do
      c_g_p_x <- app c (varR lvl) (varR (lvl + 1)) (varR (lvl + 2)) (varR (lvl + 3))
      c'_g_p_x <- app c' (varR lvl) (varR (lvl + 1)) (varR (lvl + 2)) (varR (lvl + 3))
      conv' (ns :> g :> v :> p :> x) (ns' :> g' :> v' :> p' :> x') (lvl + 4) c_g_p_x c'_g_p_x
      conv' ns ns' lvl i i'
      t_g_f_p_x <- app t (varR lvl) (varR (lvl + 1)) (varR (lvl + 2)) (varR (lvl + 3)) (varR (lvl + 4))
      t'_g_f_p_x <- app t' (varR lvl) (varR (lvl + 1)) (varR (lvl + 2)) (varR (lvl + 3)) (varR (lvl + 4))
      conv' (ns :> g :> v :> f :> p :> x) (ns' :> g' :> v' :> f' :> p' :> x') (lvl + 5) t_g_f_p_x t'_g_f_p_x
      -- TODO: this *might* be problematic in the case that exactly one of [a], [a'] is Nothing
      sequence_ (liftM2 (conv' ns ns' lvl) a a')
    conv' ns ns' lvl (VMu _ f aty cs functor a) (VMu _ f' aty' cs' functor' a') = do
      conv' ns ns' lvl aty aty'
      zipWithM_ convCons cs cs'
      sequence_ (liftM2 convFunctor functor functor')
      sequence_ (liftM2 (conv' ns ns' lvl) a a')
      where
        convCons
          :: (Name, (Binder, ValClosure (A 1), ValClosure (A 2)))
          -> (Name, (Binder, ValClosure (A 1), ValClosure (A 2)))
          -> Checker (Variant e) ()
        convCons (ci, (xi, bi, ixi)) (ci', (xi', bi', ixi'))
          | ci == ci' = do
              let vf = varR lvl
                  vxi = varR (lvl + 1)
              bi_muF <- app bi vf
              bi'_muF <- app bi' vf
              conv' (ns :> Name f) (ns' :> Name f') (lvl + 1) bi_muF bi'_muF
              ixi_muF_xi <- app ixi vf vxi
              ixi'_muF_xi <- app ixi' vf vxi
              conv' (ns :> Name f :> xi) (ns' :> Name f' :> xi') (lvl + 2) ixi_muF_xi ixi'_muF_xi
          | otherwise =
              -- TODO: consider allowing reordering of constructors in definitional equality
              throw (ConstructorMismatch ci ci' pos)
        convFunctor :: VFunctorInstance -> VFunctorInstance -> Checker (Variant e) ()
        convFunctor (VFunctorInstance a b g p x t) (VFunctorInstance a' b' g' p' x' t') = do
          t_f_a_b_g_p_x <- app t (varR lvl) (varR (lvl + 1)) (varR (lvl + 2)) (varR (lvl + 3)) (varR (lvl + 4)) (varR (lvl + 5))
          t'_f_a_b_g_p_x <- app t' (varR lvl) (varR (lvl + 1)) (varR (lvl + 2)) (varR (lvl + 3)) (varR (lvl + 4)) (varR (lvl + 5))
          conv' (ns :> Name f :> a :> b :> g :> p :> x) (ns' :> Name f' :> a' :> b' :> g' :> p' :> x') (lvl + 6) t_f_a_b_g_p_x t'_f_a_b_g_p_x
    conv' ns ns' lvl a b = do
      aTS <- TS . prettyPrintTerm ns <$> quote lvl a
      bTS <- TS . prettyPrintTerm ns' <$> quote lvl b
      throw (ConversionFailure aTS bTS pos)

    tryChoice
      :: Checker (Variant e) ()
      -> Checker (Variant e) ()
      -> Checker (Variant e) ()
      -> Checker (Variant e) ()
    tryChoice b ifTrue ifFalse = do
      b <- catchError (b >> pure True) (const (pure False))
      if b then ifTrue else ifFalse
