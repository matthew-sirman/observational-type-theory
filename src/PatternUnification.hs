{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module PatternUnification (
  solve,
) where

import Error
import Eval
import EvalProp
import MonadChecker
import PrettyPrinter
import Syntax
import Value

import Control.Monad (when)
import Control.Monad.Oops
import Data.IntMap qualified as IM
import Error.Diagnose

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
  :: e `CouldBe` ErrorDuringUnification
  => Position
  -> [Binder]
  -> Lvl
  -> Env
  -> Checker (Variant e) PartialRenaming
invert pos names gamma sub = do
  (dom, renaming) <- inv sub
  pure (PRen {renaming = renaming, dom = dom, cod = gamma})
  where
    inv :: e `CouldBe` ErrorDuringUnification => Env -> Checker (Variant e) (Lvl, IM.IntMap Lvl)
    inv [] = pure (0, IM.empty)
    inv (sub :> (Defined, _)) = do
      (dom, renaming) <- inv sub
      pure (dom + 1, renaming)
    inv (sub :> (Bound, prop -> (PVar (Lvl x)))) = do
      (dom, renaming) <- inv sub
      when (IM.member x renaming) (throw (NonLinearSpineDuplicate (show (names !! x)) pos))
      pure (dom + 1, IM.insert x dom renaming)
    inv (_ :> (Bound, Val t _)) = do
      tm <- quote gamma t
      throw (NonLinearSpineNonVariable (TS (prettyPrintTerm names tm)) pos)
    inv (_ :> (Bound, Prop p)) = do
      tm <- quoteProp gamma p
      throw (NonLinearSpineNonVariable (TS (prettyPrintTerm names tm)) pos)

renameProp
  :: forall e
   . e `CouldBe` ErrorDuringUnification
  => Position
  -> [Binder]
  -> MetaVar
  -> PartialRenaming
  -> VProp
  -> Checker (Variant e) (Term Ix)
renameProp pos ns _ sub (PVar (Lvl x)) =
  case IM.lookup x (renaming sub) of
    Nothing -> throw (EscapingVariable (show (ns !! x)) pos)
    Just x' -> pure (Var (lvl2ix (dom sub) x'))
renameProp pos _ m _ (PMeta m' _)
  | m == m' = throw (OccursCheck m pos)
  | otherwise = pure (Meta m')
renameProp _ _ _ _ (PU s) = pure (U s)
renameProp pos ns m sub (PLambda s x t) = do
  t <- renameProp pos (ns :> x) m (liftRenaming 1 sub) =<< app t (varP (cod sub))
  pure (Lambda s x t)
renameProp pos ns m sub (PApp t u) = App Irrelevant <$> renameProp pos ns m sub t <*> renameProp pos ns m sub u
renameProp pos ns m sub (PPi s x a b) = do
  a <- renameProp pos ns m sub a
  b <- renameProp pos (ns :> x) m (liftRenaming 1 sub) =<< app b (varP (cod sub))
  pure (Pi s x a b)
renameProp _ _ _ _ PZero = pure Zero
renameProp pos ns m sub (PSucc n) = Succ <$> renameProp pos ns m sub n
renameProp pos ns m sub (PNElim z a t0 x ih ts n) = do
  a <- renameProp pos (ns :> z) m (liftRenaming 1 sub) =<< app a (varP (cod sub))
  t0 <- renameProp pos ns m sub t0
  ts <- renameProp pos (ns :> x :> ih) m (liftRenaming 2 sub) =<< app ts (varP (cod sub)) (varP (cod sub + 1))
  n <- renameProp pos ns m sub n
  pure (NElim z a t0 x ih ts n)
renameProp _ _ _ _ PNat = pure Nat
renameProp pos ns m sub (PPropPair t u) = PropPair <$> renameProp pos ns m sub t <*> renameProp pos ns m sub u
renameProp pos ns m sub (PPropFst t) = PropFst <$> renameProp pos ns m sub t
renameProp pos ns m sub (PPropSnd t) = PropSnd <$> renameProp pos ns m sub t
renameProp pos ns m sub (PExists x a b) = do
  a <- renameProp pos ns m sub a
  b <- renameProp pos (ns :> x) m (liftRenaming 1 sub) =<< app b (varP (cod sub))
  pure (Exists x a b)
renameProp pos ns m sub (PAbort a t) = Abort <$> renameProp pos ns m sub a <*> renameProp pos ns m sub t
renameProp _ _ _ _ PEmpty = pure Empty
renameProp _ _ _ _ POne = pure One
renameProp _ _ _ _ PUnit = pure Unit
renameProp pos ns m sub (PEq t a u) = Eq <$> renameProp pos ns m sub t <*> renameProp pos ns m sub a <*> renameProp pos ns m sub u
renameProp pos ns m sub (PRefl t) = Refl <$> renameProp pos ns m sub t
renameProp pos ns m sub (PSym t u e) = Sym <$> renameProp pos ns m sub t <*> renameProp pos ns m sub u <*> renameProp pos ns m sub e
renameProp pos ns m sub (PTrans t u v e e') =
  Trans <$> renameProp pos ns m sub t <*> renameProp pos ns m sub u <*> renameProp pos ns m sub v <*> renameProp pos ns m sub e <*> renameProp pos ns m sub e'
renameProp pos ns m sub (PAp b x t u v e) = do
  b <- renameProp pos ns m sub b
  t <- renameProp pos (ns :> x) m (liftRenaming 1 sub) =<< app t (varP (cod sub))
  u <- renameProp pos ns m sub u
  v <- renameProp pos ns m sub v
  e <- renameProp pos ns m sub e
  pure (Ap b x t u v e)
renameProp pos ns m sub (PTransp t x pf b u t' e) = do
  t <- renameProp pos ns m sub t
  b <- renameProp pos (ns :> x :> pf) m (liftRenaming 2 sub) =<< app b (varP (cod sub)) (varP (cod sub + 1))
  u <- renameProp pos ns m sub u
  t' <- renameProp pos ns m sub t'
  e <- renameProp pos ns m sub e
  pure (Transp t x pf b u t' e)
renameProp pos ns m sub (PCast a b e t) = do
  a <- renameProp pos ns m sub a
  b <- renameProp pos ns m sub b
  e <- renameProp pos ns m sub e
  t <- renameProp pos ns m sub t
  pure (Cast a b e t)
renameProp pos ns m sub (PPair t u) = Pair <$> renameProp pos ns m sub t <*> renameProp pos ns m sub u
renameProp pos ns m sub (PFst t) = Fst <$> renameProp pos ns m sub t
renameProp pos ns m sub (PSnd t) = Snd <$> renameProp pos ns m sub t
renameProp pos ns m sub (PSigma x a b) = do
  a <- renameProp pos ns m sub a
  b <- renameProp pos (ns :> x) m (liftRenaming 1 sub) =<< app b (varP (cod sub))
  pure (Sigma x a b)
renameProp pos ns m sub (PQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) = do
  a <- renameProp pos ns m sub a
  r <- renameProp pos (ns :> x :> y) m (liftRenaming 2 sub) =<< app r (varP (cod sub)) (varP (cod sub + 1))
  rr <- renameProp pos (ns :> rx) m (liftRenaming 1 sub) =<< app rr (varP (cod sub))
  rs <- renameProp pos (ns :> sx :> sy :> sxy) m (liftRenaming 3 sub) =<< app rs (varP (cod sub)) (varP (cod sub + 1)) (varP (cod sub + 2))
  rt <- renameProp pos (ns :> tx :> ty :> tz :> txy :> tyz) m (liftRenaming 5 sub) =<< app rt (varP (cod sub)) (varP (cod sub + 1)) (varP (cod sub + 2)) (varP (cod sub + 3)) (varP (cod sub + 4))
  pure (Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)
renameProp pos ns m sub (PQProj t) = QProj <$> renameProp pos ns m sub t
renameProp pos ns m sub (PQElim z b x tpi px py pe p u) = do
  b <- renameProp pos (ns :> z) m (liftRenaming 1 sub) =<< app b (varP (cod sub))
  tpi <- renameProp pos (ns :> x) m (liftRenaming 1 sub) =<< app tpi (varP (cod sub))
  p <- renameProp pos (ns :> px :> py :> pe) m (liftRenaming 3 sub) =<< app p (varP (cod sub)) (varP (cod sub + 1)) (varP (cod sub + 2))
  u <- renameProp pos ns m sub u
  pure (QElim z b x tpi px py pe p u)
renameProp pos ns m sub (PIdRefl t) = IdRefl <$> renameProp pos ns m sub t
renameProp pos ns m sub (PIdPath e) = IdPath <$> renameProp pos ns m sub e
renameProp pos ns m sub (PJ a t x pf b u v e) = do
  a <- renameProp pos ns m sub a
  t <- renameProp pos ns m sub t
  b <- renameProp pos (ns :> x :> pf) m (liftRenaming 2 sub) =<< app b (varP (cod sub)) (varP (cod sub + 1))
  u <- renameProp pos ns m sub u
  v <- renameProp pos ns m sub v
  e <- renameProp pos ns m sub e
  pure (J a t x pf b u v e)
renameProp pos ns m sub (PId a t u) = Id <$> renameProp pos ns m sub a <*> renameProp pos ns m sub t <*> renameProp pos ns m sub u
renameProp pos ns m sub (PBoxProof e) = BoxProof <$> renameProp pos ns m sub e
renameProp pos ns m sub (PBoxElim t) = BoxElim <$> renameProp pos ns m sub t
renameProp pos ns m sub (PBox a) = Box <$> renameProp pos ns m sub a
renameProp _ _ _ _ PROne = pure ROne
renameProp _ _ _ _ PRUnit = pure RUnit
renameProp pos ns m sub (PCons c t e) = Cons c <$> renameProp pos ns m sub t <*> renameProp pos ns m sub e
renameProp pos ns m sub (PIn t) = In <$> renameProp pos ns m sub t
renameProp pos ns m sub (PFLift f a) = FLift <$> renameProp pos ns m sub f <*> renameProp pos ns m sub a
renameProp pos ns m sub (PFmap f a b g p x) = do
  f <- renameProp pos ns m sub f
  a <- renameProp pos ns m sub a
  b <- renameProp pos ns m sub b
  g <- renameProp pos ns m sub g
  p <- renameProp pos ns m sub p
  x <- renameProp pos ns m sub x
  pure (Fmap f a b g p x)
renameProp pos ns m sub (PMatch t x c bs) = do
  c <- renameProp pos (ns :> x) m (liftRenaming 1 sub) =<< app c (varP (cod sub))
  t <- renameProp pos ns m sub t
  bs <- mapM quoteBranch bs
  pure (Match t x c bs)
  where
    quoteBranch
      :: (Name, Binder, Binder, PropClosure (A 2))
      -> Checker (Variant e) (Name, Binder, Binder, Term Ix)
    quoteBranch (c, x, e, t) = do
      t <- renameProp pos (ns :> x :> e) m (liftRenaming 2 sub) =<< app t (varP (cod sub)) (varP (cod sub + 1))
      pure (c, x, e, t)
renameProp pos ns m sub (PFixedPoint i g v f p x c t) = do
  i <- renameProp pos ns m sub i
  c <- renameProp pos (ns :> g :> v :> p :> x) m (liftRenaming 4 sub) =<< app c (varP (cod sub)) (varP (cod sub + 1)) (varP (cod sub + 2)) (varP (cod sub + 3))
  t <- renameProp pos (ns :> g :> v :> f :> p :> x) m (liftRenaming 5 sub) =<< app t (varP (cod sub)) (varP (cod sub + 1)) (varP (cod sub + 2)) (varP (cod sub + 3)) (varP (cod sub + 4))
  pure (FixedPoint i g v f p x c t)
renameProp pos ns m sub (PMu tag f t cs functor) = do
  t <- renameProp pos ns m sub t
  cs <- mapM renameCons cs
  functor <- mapM renameFunctor functor
  pure (Mu tag f t cs functor)
  where
    renameCons
      :: (Name, Binder, PropClosure (A 1), PropClosure (A 2))
      -> Checker (Variant e) (Name, Binder, Term Ix, Name, Term Ix)
    renameCons (ci, xi, bi, ixi) = do
      bi <- renameProp pos (ns :> Name f) m (liftRenaming 1 sub) =<< app bi (varP (cod sub))
      ixi <- renameProp pos (ns :> Name f :> xi) m (liftRenaming 2 sub) =<< app ixi (varP (cod sub)) (varP (cod sub + 1))
      pure (ci, xi, bi, f, ixi)

    renameFunctor :: PFunctorInstance -> Checker (Variant e) (FunctorInstance Ix)
    renameFunctor (PFunctorInstance a b g p x t) = do
      t <- renameProp pos (ns :> Name f :> a :> b :> g :> p :> x) m (liftRenaming 6 sub) =<< app t (varP (cod sub)) (varP (cod sub + 1)) (varP (cod sub + 2)) (varP (cod sub + 3)) (varP (cod sub + 4)) (varP (cod sub + 5))
      pure (FunctorInstanceF a b g p x t)
renameProp pos ns m sub (PLet x s a t u) = do
  a <- renameProp pos ns m sub a
  t <- renameProp pos ns m sub t
  u <- renameProp pos (ns :> x) m (liftRenaming 1 sub) =<< app u (varP (cod sub))
  pure (Let x s a t u)
renameProp pos ns m sub (PAnnotation t a) = Annotation <$> renameProp pos ns m sub t <*> renameProp pos ns m sub a

renameSp
  :: forall e
   . e `CouldBe` ErrorDuringUnification
  => Position
  -> [Binder]
  -> MetaVar
  -> PartialRenaming
  -> Term Ix
  -> VSpine
  -> Checker (Variant e) (Term Ix)
renameSp _ _ _ _ base [] = pure base
renameSp pos ns m sub base (sp :> VApp u) = do
  sp <- renameSp pos ns m sub base sp
  u <- rename pos ns m sub u
  pure (App Relevant sp u)
renameSp pos ns m sub base (sp :> VAppProp p) = do
  sp <- renameSp pos ns m sub base sp
  p <- renameProp pos ns m sub p
  pure (App Irrelevant sp p)
renameSp pos ns m sub base (sp :> VNElim z a t0 x ih ts) = do
  sp <- renameSp pos ns m sub base sp
  a <- rename pos (ns :> z) m (liftRenaming 1 sub) =<< app a (varR (cod sub))
  t0 <- rename pos ns m sub t0
  ts <- rename pos (ns :> x :> ih) m (liftRenaming 2 sub) =<< app ts (varR (cod sub)) (varR (cod sub + 1))
  pure (NElim z a t0 x ih ts sp)
renameSp pos ns m sub base (sp :> VFst) = do
  sp <- renameSp pos ns m sub base sp
  pure (Fst sp)
renameSp pos ns m sub base (sp :> VSnd) = do
  sp <- renameSp pos ns m sub base sp
  pure (Snd sp)
renameSp pos ns m sub base (sp :> VQElim z b x tpi px py pe p) = do
  sp <- renameSp pos ns m sub base sp
  b <- rename pos (ns :> z) m (liftRenaming 1 sub) =<< app b (varR (cod sub))
  tpi <- rename pos (ns :> x) m (liftRenaming 1 sub) =<< app tpi (varR (cod sub))
  p <- renameProp pos ns m sub =<< app p (varP (cod sub)) (varP (cod sub + 1)) (varP (cod sub + 2))
  pure (QElim z b x tpi px py pe p sp)
renameSp pos ns m sub base (sp :> VJ a t x pf b u v) = do
  sp <- renameSp pos ns m sub base sp
  a <- rename pos ns m sub a
  t <- rename pos ns m sub t
  b <- rename pos ns m (liftRenaming 2 sub) =<< app b (varR (cod sub)) (varR (cod sub + 1))
  u <- rename pos ns m sub u
  v <- rename pos ns m sub v
  pure (J a t x pf b u v sp)
renameSp pos ns m sub base (sp :> VBoxElim) = do
  sp <- renameSp pos ns m sub base sp
  pure (BoxElim sp)
renameSp pos ns m sub base (sp :> VMatch x c bs) = do
  sp <- renameSp pos ns m sub base sp
  c <- rename pos (ns :> x) m (liftRenaming 1 sub) =<< app c (varR (cod sub))
  bs <- mapM renameBranch bs
  pure (Match sp x c bs)
  where
    renameBranch
      :: (Name, Binder, Binder, ValClosure (A 2))
      -> Checker (Variant e) (Name, Binder, Binder, Term Ix)
    renameBranch (c, x, e, t) =
      (c,x,e,) <$> (rename pos ns m (liftRenaming 2 sub) =<< app t (varR (cod sub)) (varR (cod sub + 1)))

rename
  :: forall e
   . e `CouldBe` ErrorDuringUnification
  => Position
  -> [Binder]
  -> MetaVar
  -> PartialRenaming
  -> Val
  -> Checker (Variant e) (Term Ix)
rename pos ns m sub (VNeutral ne sp) = do
  ne <- rename pos ns m sub ne
  renameSp pos ns m sub ne sp
rename pos ns _ sub (VRigid (Lvl x)) =
  case IM.lookup x (renaming sub) of
    Nothing -> throw (EscapingVariable (show (ns !! x)) pos)
    Just x' -> pure (Var (lvl2ix (dom sub) x'))
rename pos _ m _ (VFlex m' _)
  -- TODO: Need to in fact check DAG ordering, not just single MetaVar occurrence.
  -- e.g. might have α := λx. β, β := α (neither directly violate occurs check, but clearly
  -- unsolvable)
  --
  -- POSSIBILITY: throw occurs check if [m' <= m] (i.e. [m'] was created first,
  -- and as such [m] might depend on it)
  | m == m' = throw (OccursCheck m pos)
  | otherwise = pure (Meta m')
rename _ _ _ _ (VU s) = pure (U s)
rename pos ns m sub (VLambda s x t) =
  Lambda s x <$> (rename pos (ns :> x) m (liftRenaming 1 sub) =<< app t (var s (cod sub)))
rename pos ns m sub (VPi s x a b) = do
  a <- rename pos ns m sub a
  b <- rename pos (ns :> x) m (liftRenaming 1 sub) =<< app b (varR (cod sub))
  pure (Pi s x a b)
rename _ _ _ _ VZero = pure Zero
rename pos ns m sub (VSucc n) = Succ <$> rename pos ns m sub n
rename _ _ _ _ VNat = pure Nat
rename pos ns m sub (VExists x a b) = do
  a <- rename pos ns m sub a
  b <- rename pos (ns :> x) m (liftRenaming 1 sub) =<< app b (varR (cod sub))
  pure (Exists x a b)
rename pos ns m sub (VAbort a t) = do
  a <- rename pos ns m sub a
  t <- renameProp pos ns m sub t
  pure (Abort a t)
rename _ _ _ _ VEmpty = pure Empty
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
  b <- rename pos (ns :> x) m (liftRenaming 1 sub) =<< app b (varR (cod sub))
  pure (Sigma x a b)
rename pos ns m sub (VQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) = do
  a <- rename pos ns m sub a
  r <- rename pos (ns :> x :> y) m (liftRenaming 2 sub) =<< app r (varR (cod sub)) (varR (cod sub + 1))
  rr <- renameProp pos ns m sub =<< app rr (varP (cod sub))
  rs <- renameProp pos ns m sub =<< app rs (varP (cod sub)) (varP (cod sub + 1)) (varP (cod sub + 3))
  rt <- renameProp pos ns m sub =<< app rt (varP (cod sub)) (varP (cod sub + 1)) (varP (cod sub + 3)) (varP (cod sub + 3)) (varP (cod sub + 4))
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
rename _ _ _ _ VROne = pure ROne
rename _ _ _ _ VRUnit = pure RUnit
rename pos ns m sub (VCons c t e) = do
  t <- rename pos ns m sub t
  e <- renameProp pos ns m sub e
  pure (Cons c t e)
rename pos ns m sub (VIn t) = In <$> rename pos ns m sub t
rename pos ns m sub (VFLift f a) = do
  f <- rename pos ns m sub f
  a <- rename pos ns m sub a
  pure (FLift f a)
rename pos ns m sub (VFmap f a b g p x) = do
  f <- rename pos ns m sub f
  a <- rename pos ns m sub a
  b <- rename pos ns m sub b
  g <- rename pos ns m sub g
  p <- rename pos ns m sub p
  x <- rename pos ns m sub x
  pure (Fmap f a b g p x)
rename pos ns m sub (VFixedPoint i g v f p x c t a) = do
  i <- rename pos ns m sub i
  c_g_p_x <- app c (varR (cod sub)) (varR (cod sub + 1)) (varR (cod sub + 2)) (varR (cod sub + 3))
  t_g_f_p_x <- app t (varR (cod sub)) (varR (cod sub + 1)) (varR (cod sub + 2)) (varR (cod sub + 3)) (varR (cod sub + 4))
  c <- rename pos (ns :> g :> v :> p :> x) m (liftRenaming 4 sub) c_g_p_x
  t <- rename pos (ns :> g :> v :> f :> p :> x) m (liftRenaming 5 sub) t_g_f_p_x
  let fix_f = FixedPoint i g v f p x c t
  case a of
    Nothing -> pure fix_f
    Just a -> App Relevant fix_f <$> rename pos ns m sub a
rename pos ns m sub (VMu tag f aty cs functor a) = do
  fty <- rename pos ns m sub aty
  cs <- mapM renameCons cs
  functor <- mapM renameFunctor functor
  let muF = Mu tag f fty cs functor
  case a of
    Nothing -> pure muF
    Just a -> App Relevant muF <$> rename pos ns m sub a
  where
    renameCons
      :: (Name, (Binder, ValClosure (A 1), ValClosure (A 2)))
      -> Checker (Variant e) (Name, Binder, Type Ix, Name, Type Ix)
    renameCons (ci, (xi, bi, ixi)) = do
      bi_f <- app bi (varR (cod sub))
      bi <- rename pos (ns :> Name f) m (liftRenaming 1 sub) bi_f
      ixi_f_xi <- app ixi (varR (cod sub)) (varR (cod sub + 1))
      ixi <- rename pos (ns :> Name f :> xi) m (liftRenaming 2 sub) ixi_f_xi
      pure (ci, xi, bi, f, ixi)

    renameFunctor :: VFunctorInstance -> Checker (Variant e) (FunctorInstance Ix)
    renameFunctor (VFunctorInstance a b g p x t) = do
      t_f_a_b_g_p_x <- app t (varR (cod sub)) (varR (cod sub + 1)) (varR (cod sub + 2)) (varR (cod sub + 3)) (varR (cod sub + 4)) (varR (cod sub + 5))
      t <- rename pos (ns :> Name f :> a :> b :> g :> p :> x) m (liftRenaming 6 sub) t_f_a_b_g_p_x
      pure (FunctorInstanceF a b g p x t)

-- Solve a metavariable, possibly applied to a spine of eliminators
solve
  :: e `CouldBe` ErrorDuringUnification
  => Position
  -> [Binder]
  -> Lvl
  -> MetaVar
  -> Env
  -> VSpine
  -> Val
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
  u <- embedVal u
  solve pos names lvl body (sub :> (Bound, u)) sp t
  addSolution mv (Lambda Relevant (names !! x) (Meta body))
solve pos names lvl mv sub (sp :> VAppProp p@(PVar (Lvl x))) t = do
  body <- freshMeta names
  solve pos names lvl body (sub :> (Bound, Prop p)) sp t
  addSolution mv (Lambda Irrelevant (names !! x) (Meta body))
solve pos names lvl _ _ (_ :> VApp u) _ = do
  tm <- quote lvl u
  throw (NonLinearSpineNonVariable (TS (prettyPrintTerm names tm)) pos)
solve pos names lvl _ _ (_ :> VAppProp p) _ = do
  tm <- quoteProp lvl p
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
