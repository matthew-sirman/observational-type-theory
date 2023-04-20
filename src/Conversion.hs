{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
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

import Control.Monad (liftM2, zipWithM_)
import Control.Monad.Oops
import Error.Diagnose

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
  -> Val
  -> Val
  -> Checker (Variant e) ()
conv pos names = conv' names names
  where
    convSp
      :: [Binder]
      -> [Binder]
      -> Lvl
      -> VSpine
      -> VSpine
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
        -- TODO: don't assume same ordering
        convBranch
          :: (Name, Binder, Binder, Closure (A 2) Val)
          -> (Name, Binder, Binder, Closure (A 2) Val)
          -> Checker (Variant e) ()
        convBranch (c, x, e, t) (c', x', e', t')
          | c == c' = do
              let vx = VVar lvl
                  ve = VVar (lvl + 1)
              t <- app' t vx ve
              t' <- app' t' vx ve
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
      :: [Binder] -> [Binder] -> Lvl -> Val -> Val -> Checker (Variant e) ()
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
    conv' _ _ _ (VProp {}) _ = pure ()
    conv' _ _ _ _ (VProp {}) = pure ()
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
    conv' ns ns' lvl (VCons c t _) (VCons c' t' _)
      | c == c' = do
          conv' ns ns' lvl t t'
    conv' ns ns' lvl (VFixedPoint i g f p x c t a sp) (VFixedPoint i' g' f' p' x' c' t' a' sp') = do
      c_g_p_x <- app' c (VVar lvl) (VVar (lvl + 1)) (VVar (lvl + 2))
      c'_g_p_x <- app' c' (VVar lvl) (VVar (lvl + 1)) (VVar (lvl + 2))
      conv' (ns :> g :> p :> x) (ns' :> g' :> p' :> x') (lvl + 3) c_g_p_x c'_g_p_x
      conv' ns ns' lvl i i'
      t_g_f_p_x <- app' t (VVar lvl) (VVar (lvl + 1)) (VVar (lvl + 2)) (VVar (lvl + 3))
      t'_g_f_p_x <- app' t' (VVar lvl) (VVar (lvl + 1)) (VVar (lvl + 2)) (VVar (lvl + 3))
      conv' (ns :> g :> f :> p :> x) (ns' :> g' :> f' :> p' :> x') (lvl + 4) t_g_f_p_x t'_g_f_p_x
      -- TODO: this *might* be problematic in the case that exactly one of [a], [a'] is Nothing
      sequence_ (liftM2 (conv' ns ns' lvl) a a')
      convSp ns ns' lvl sp sp'
    conv' ns ns' lvl (VMu _ f fty x cs a) (VMu _ f' fty' x' cs' a') = do
      conv' ns ns' lvl fty fty'
      zipWithM_ convCons cs cs'
      sequence_ (liftM2 (conv' ns ns' lvl) a a')
      where
        convCons
          :: (Name, (Relevance, Binder, Closure (A 2) Val, Closure (A 3) Val))
          -> (Name, (Relevance, Binder, Closure (A 2) Val, Closure (A 3) Val))
          -> Checker (Variant e) ()
        convCons (ci, (si, xi, bi, ixi)) (ci', (si', xi', bi', ixi'))
          | ci == ci' = do
              convSort pos si si'
              let vf = VVar lvl
                  vx = VVar (lvl + 1)
                  vxi = VVar (lvl + 2)
              bi_muF_x <- app' bi vf vx
              bi'_muF_x <- app' bi' vf vx
              conv' (ns :> Name f :> x) (ns' :> Name f' :> x') (lvl + 2) bi_muF_x bi'_muF_x
              ixi_muF_x_xi <- app' ixi vf vx vxi
              ixi'_muF_x_xi <- app' ixi' vf vx vxi
              conv' (ns :> Name f :> x :> xi) (ns' :> Name f' :> x' :> xi') (lvl + 3) ixi_muF_x_xi ixi'_muF_x_xi
          | otherwise =
              -- TODO: consider allowing reordering of constructors in definitional equality
              throw (ConstructorMismatch ci ci' pos)
    conv' _ _ _ (VBoxProof _) (VBoxProof _) = pure ()
    conv' ns ns' lvl (VBox a) (VBox a') = conv' ns ns' lvl a a'
    conv' ns ns' lvl a b = do
      aTS <- TS . prettyPrintTerm ns <$> quote lvl a
      bTS <- TS . prettyPrintTerm ns' <$> quote lvl b
      throw (ConversionFailure aTS bTS pos)