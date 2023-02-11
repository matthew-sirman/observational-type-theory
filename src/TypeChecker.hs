{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module TypeChecker where

import Control.Monad.Except
import Control.Monad.Oops (throw)
import Data.Function ((&))
import Data.Variant hiding (throw)
import Error.Diagnose

import Error
import Syntax

type Checker e a = Except e a

type Types = [(Name, (Relevance, VTy Ix))]

data Context = Context
  { env :: Env Ix
  , types :: Types
  , lvl :: Lvl
  }

names :: Context -> [Name]
names = map fst . types

emptyContext :: Context
emptyContext = Context {env = [], types = [], lvl = 0}

eqReduce :: Val Ix -> VTy Ix -> Val Ix -> Val Ix
eqReduce vt va vu = eqReduceType va
  where
    -- Initially driven just by the type

    eqReduceType :: VTy Ix -> Val Ix
    -- Rule Eq-Fun
    eqReduceType (VPi s x a b) =
      let fx_eq_gx vx = eqReduce (vt $$ VApp vx) (b vx) (vu $$ VApp vx)
       in VPi s x a fx_eq_gx
    -- Rule Eq-Ω
    eqReduceType (VU Irrelevant) =
      let t_to_u = vFun Irrelevant vt vu
          u_to_t = vFun Irrelevant vu vt
       in vAnd t_to_u u_to_t
    -- Rule Id-Proof-Eq
    eqReduceType (VId {}) = VUnit
    -- Other cases require matching on [t] and [u]
    eqReduceType va = eqReduceAll vt va vu
    --
    -- Then driven by terms and type
    eqReduceAll :: Val Ix -> VTy Ix -> Val Ix -> Val Ix
    -- Rules Eq-Univ and Eq-Univ-≠
    eqReduceAll vt (VU Relevant) vu
      | headNeq vt vu = VEmpty
    eqReduceAll VNat (VU Relevant) VNat = VUnit
    eqReduceAll (VU s) (VU Relevant) (VU s')
      | s == s' = VUnit
      | otherwise = VEmpty
    -- Rule Eq-Π
    eqReduceAll (VPi s _ a b) (VU Relevant) (VPi s' x' a' b')
      | s == s' =
          let a_eq_a' = eqReduce a (VU Relevant) a'
              b_eq_b' _ =
                VPi
                  s
                  x'
                  a'
                  (\v -> eqReduce (b (cast a' a v)) (VU Relevant) (b' v))
           in VExists "e" a_eq_a' b_eq_b'
    -- Rule Eq-Σ
    eqReduceAll (VSigma _ a b) (VU Relevant) (VSigma x' a' b') =
      let a_eq_a' = eqReduce a (VU Relevant) a'
          b_eq_b' v = eqReduce (b (cast a' a v)) (VU Relevant) (b' v)
       in VExists "e" a_eq_a' (\_ -> VPi Relevant x' a' b_eq_b')
    -- Rule Eq-Quotient
    eqReduceAll (VQuotient a x y r) (VU Relevant) (VQuotient a' _ _ r') =
      let a_eq_a' = eqReduce a (VU Relevant) a'
          rxy_eq_rx'y' vx vy =
            eqReduce
              (r vx vy)
              (VU Irrelevant)
              (r' (cast a a' vx) (cast a a' vy))
       in VExists
            "e"
            a_eq_a'
            (\_ -> VPi Relevant x a (VPi Relevant y a . rxy_eq_rx'y'))
    -- Rule Eq-Zero
    eqReduceAll VZero VNat VZero = VUnit
    -- Rule Eq-Zero-Succ
    eqReduceAll VZero VNat (VSucc _) = VEmpty
    -- Rule Eq-Succ-Zero
    eqReduceAll (VSucc _) VNat VZero = VEmpty
    -- Rule Eq-Succ
    eqReduceAll (VSucc m) VNat (VSucc n) = eqReduceAll m VNat n
    -- Rule Eq-Pair
    eqReduceAll (VPair t u) (VSigma _ a b) (VPair t' u') =
      let t_eq_t' = eqReduce t a t'
          u_eq_u' _ = eqReduce (cast (b t) (b t') u) (b t') u'
       in VExists "e" t_eq_t' u_eq_u'
    -- Rule Quotient-Proj-Eq
    eqReduceAll (VQProj t) (VQuotient _ _ _ r) (VQProj u) = r t u
    -- Rule Id-Eq
    eqReduceAll (VId a t u) (VU Relevant) (VId a' t' u') =
      let a_eq_a' = eqReduce a (VU Relevant) a'
          t_eq_t' = eqReduce (cast a a' t) a' t'
          u_eq_u' = eqReduce (cast a a' u) a' u'
       in VExists "e" a_eq_a' (\_ -> vAnd t_eq_t' u_eq_u')
    -- No reduction rule
    eqReduceAll t a u = VEq t a u
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

cast :: VTy Ix -> VTy Ix -> Val Ix -> Val Ix
-- Rule Cast-Zero
cast VNat VNat VZero = VZero
-- Rule Cast-Succ
cast VNat VNat (VSucc n) = VSucc (cast VNat VNat n)
-- Rule Cast-Univ
cast (VU s) (VU s') a
  | s == s' = a
-- Rule Cast-Pi
cast (VPi _ _ a b) (VPi _ x' a' b') f =
  let cast_a'_a = cast a' a
   in VLambda
        x'
        ( \va' ->
            let a = cast_a'_a va'
             in cast (b a) (b' va') (f $$ VApp a)
        )
cast (VSigma _ a b) (VSigma _ a' b') (VPair t u) =
  let t' = cast a a' t
      u' = cast (b t) (b' t') u
   in VPair t' u'
cast (VSigma _ a b) (VSigma _ a' b') t =
  let t' = cast a a' (t $$ VFst)
      u' = cast (b t) (b' t') (t $$ VSnd)
   in VPair t' u'
cast (VQuotient a _ _ _) (VQuotient a' _ _ _) (VQProj t) = VQProj (cast a a' t)
cast (VId {}) (VId {}) (VIdRefl _) = VIdPath
cast (VId {}) (VId {}) VIdPath = VIdPath
cast a b t = VCast a b t

eval :: Env Ix -> Term Ix -> Val Ix
eval env (Var (Ix x)) = env !! x
eval _ (U s) = VU s
eval env (Lambda x e) = VLambda x (\vx -> eval (env :> vx) e)
eval env (App t u) = eval env t $$ VApp (eval env u)
eval env (Pi s x a b) = VPi s x (eval env a) (\vx -> eval (env :> vx) b)
eval _ Zero = VZero
eval env (Succ n) = VSucc (eval env n)
eval env (NElim z a t0 x ih ts n) = eval env n $$ elim
  where
    va :: Closure1 Ix
    va vz = eval (env :> vz) a
    vt0 :: Val Ix
    vt0 = eval env t0
    vts :: Closure2 Ix
    vts vx vih = eval (env :> vx :> vih) ts
    elim :: VElim Ix
    elim = VNElim z va vt0 x ih vts
eval _ Nat = VNat
eval _ (PropPair {}) = VOne
eval _ (PropFst _) = VOne
eval _ (PropSnd _) = VOne
eval env (Exists x a b) = VExists x (eval env a) (\v -> eval (env :> v) b)
eval env (Abort a _) = VAbort (eval env a)
eval _ Empty = VEmpty
eval _ One = VOne
eval _ Unit = VUnit
eval env (Eq t a u) = eqReduce (eval env t) (eval env a) (eval env u)
eval _ (Refl _) = VOne
eval _ (Transp {}) = VOne
eval env (Cast a b _ t) = cast (eval env a) (eval env b) (eval env t)
eval _ (CastRefl {}) = VOne
eval env (Pair t u) = VPair (eval env t) (eval env u)
eval env (Fst p) = eval env p $$ VFst
eval env (Snd p) = eval env p $$ VSnd
eval env (Sigma x a b) = VSigma x (eval env a) (\vx -> eval (env :> vx) b)
eval env (Quotient a x y r _ _ _ _ _ _ _ _ _ _ _ _) =
  VQuotient (eval env a) x y (\vx vy -> eval (env :> vx :> vy) r)
eval env (QProj t) = VQProj (eval env t)
eval env (QElim z b x tpi _ _ _ _ u) = eval env u $$ VQElim z vb x vtpi
  where
    vb :: Closure1 Ix
    vb vz = eval (env :> vz) b

    vtpi :: Closure1 Ix
    vtpi vx = eval (env :> vx) tpi
eval env (IdRefl t) = VIdRefl (eval env t)
eval _ (IdPath _) = VIdPath
eval env (J a t x pf b u t' e) = eval env e $$ VJ va vt x pf vb vu vt'
  where
    va, vt, vu, vt' :: Val Ix
    va = eval env a
    vt = eval env t
    vu = eval env u
    vt' = eval env t'

    vb :: Closure2 Ix
    vb vx vpf = eval (env :> vx :> vpf) b
eval env (Id a t u) = VId (eval env a) (eval env t) (eval env u)
eval env (Let _ _ t u) =
  let vt = eval env t
   in eval (env :> vt) u
eval env (Annotation t _) = eval env t

infixl 8 $$

($$) :: Val Ix -> VElim Ix -> Val Ix
(VLambda _ c) $$ (VApp u) = c u
VZero $$ (VNElim _ _ t0 _ _ _) = t0
(VSucc n) $$ elim@(VNElim _ _ _ _ _ ts) = ts n (n $$ elim)
(VPair t _) $$ VFst = t
(VPair _ u) $$ VSnd = u
(VQProj t) $$ (VQElim _ _ _ tpi) = tpi t
(VIdRefl _) $$ (VJ _ _ _ _ _ u _) = u
VIdPath $$ (VJ _ t _ _ b u t') =
  let b_t_idrefl_t = b t (VIdRefl t)
      b_t'_idpath_e = b t' VIdPath
   in cast b_t_idrefl_t b_t'_idpath_e u
VOne $$ _ = VOne
(VRigid x sp) $$ u = VRigid x (sp :> u)
_ $$ _ = error "BUG! The impossible happened!"

quoteSp :: Lvl -> Term Ix -> VSpine Ix -> Term Ix
quoteSp _ base [] = base
quoteSp l base (sp :> VApp u) = App (quoteSp l base sp) (quote l u)
quoteSp l base (sp :> VNElim z a t0 x ih ts) =
  NElim z a' (quote l t0) x ih ts' (quoteSp l base sp)
  where
    a', ts' :: Term Ix
    a' = quote (l + 1) (a (VVar l))
    ts' = quote (l + 2) (ts (VVar l) (VVar (l + 1)))
quoteSp l base (sp :> VFst) = Fst (quoteSp l base sp)
quoteSp l base (sp :> VSnd) = Snd (quoteSp l base sp)
quoteSp l base (sp :> VQElim z b x tpi) =
  QElim
    z
    (quote (l + 1) (b (VVar l)))
    x
    (quote (l + 1) (tpi (VVar l)))
    "_"
    "_"
    "_"
    One
    (quoteSp l base sp)
quoteSp l base (sp :> VJ a t x pf b u v) = J a' t' x pf b' u' v' e'
  where
    a', t', b', u', v', e' :: Term Ix
    a' = quote l a
    t' = quote l t
    b' = quote (l + 2) (b (VVar l) (VVar (l + 1)))
    u' = quote l u
    v' = quote l v
    e' = quoteSp l base sp

quote :: Lvl -> Val Ix -> Term Ix
quote lvl@(Lvl l) (VRigid (Lvl x) sp) = quoteSp lvl (Var (Ix (l - x - 1))) sp
quote _ (VU s) = U s
quote lvl (VLambda x t) = Lambda x (quote (lvl + 1) (t (VVar lvl)))
quote lvl (VPi s x a b) = Pi s x (quote lvl a) (quote (lvl + 1) (b (VVar lvl)))
quote _ VZero = Zero
quote lvl (VSucc t) = Succ (quote lvl t)
quote _ VNat = Nat
quote lvl (VExists x a b) =
  Exists x (quote lvl a) (quote (lvl + 1) (b (VVar lvl)))
quote lvl (VAbort a) = Abort (quote lvl a) One
quote _ VEmpty = Empty
quote _ VOne = One
quote _ VUnit = Unit
quote lvl (VEq t a u) = Eq (quote lvl t) (quote lvl a) (quote lvl u)
quote lvl (VCast a b t) = Cast (quote lvl a) (quote lvl b) One (quote lvl t)
quote lvl (VPair t u) = Pair (quote lvl t) (quote lvl u)
quote lvl (VSigma x a b) =
  Sigma x (quote lvl a) (quote (lvl + 1) (b (VVar lvl)))
quote lvl (VQuotient a x y r) =
  Quotient
    (quote lvl a)
    x
    y
    (quote (lvl + 2) (r (VVar lvl) (VVar (lvl + 1))))
    "_"
    One
    "_"
    "_"
    "_"
    One
    "_"
    "_"
    "_"
    "_"
    "_"
    One
quote lvl (VQProj t) = QProj (quote lvl t)
quote lvl (VIdRefl t) = IdRefl (quote lvl t)
quote _ VIdPath = IdPath One
quote lvl (VId a t u) = Id (quote lvl a) (quote lvl t) (quote lvl u)

normalForm :: Env Ix -> Term Ix -> Term Ix
normalForm env t = quote (Lvl (length env)) (eval env t)

bind :: Name -> Relevance -> VTy Ix -> Context -> Context
bind x s tty ctx =
  ctx
    { types = types ctx :> (x, (s, tty))
    , lvl = lvl ctx + 1
    , env = env ctx :> VVar (lvl ctx)
    }

bindR, bindP :: Name -> VTy Ix -> Context -> Context
bindR x = bind x Relevant
bindP x = bind x Irrelevant

define :: Name -> Val Ix -> Relevance -> VTy Ix -> Context -> Context
define x t s tty ctx =
  ctx
    { types = types ctx :> (x, (s, tty))
    , lvl = lvl ctx + 1
    , env = env ctx :> t
    }

mapHead :: (a -> a) -> [a] -> [a]
mapHead _ [] = []
mapHead f (x : xs) = f x : xs

conv
  :: forall e
   . CouldBe e ConversionError
  => Position
  -> [Name]
  -> Lvl
  -> Val Ix
  -> Val Ix
  -> Checker (Variant e) ()
conv pos names = conv' names names
  where
    convSp
      :: [Name]
      -> [Name]
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
      conv' (ns :> z) (ns' :> z') (lvl + 1) (a (VVar lvl)) (a' (VVar lvl))
      conv' ns ns' lvl t0 t0'
      conv'
        (ns :> x :> ih)
        (ns' :> x' :> ih')
        (lvl + 2)
        (ts (VVar lvl) (VVar (lvl + 1)))
        (ts' (VVar lvl) (VVar (lvl + 1)))
    convSp ns ns' lvl (sp :> VFst) (sp' :> VFst) = convSp ns ns' lvl sp sp'
    convSp ns ns' lvl (sp :> VSnd) (sp' :> VSnd) = convSp ns ns' lvl sp sp'
    convSp ns ns' lvl (sp :> VQElim z b x tpi) (sp' :> VQElim z' b' x' tpi') = do
      convSp ns ns' lvl sp sp'
      conv' (ns :> z) (ns' :> z') (lvl + 1) (b (VVar lvl)) (b' (VVar lvl))
      conv' (ns :> x) (ns' :> x') (lvl + 1) (tpi (VVar lvl)) (tpi' (VVar lvl))
    convSp ns ns' lvl (sp :> VJ a t x pf b u v) (sp' :> VJ a' t' x' pf' b' u' v') = do
      convSp ns ns' lvl sp sp'
      conv' ns ns' lvl a a'
      conv' ns ns' lvl t t'
      conv'
        (ns :> x :> pf)
        (ns' :> x' :> pf')
        (lvl + 2)
        (b (VVar lvl) (VVar (lvl + 1)))
        (b' (VVar lvl) (VVar (lvl + 1)))
      conv' ns ns' lvl u u'
      conv' ns ns' lvl v v'
    convSp _ _ _ sp sp' =
      throw (RigidSpineMismatch (TS . showElimHead <$> safeHead sp) (TS . showElimHead <$> safeHead sp') pos)
      where
        safeHead :: [a] -> Maybe a
        safeHead [] = Nothing
        safeHead (hd : _) = Just hd

    -- Conversion checking
    conv'
      :: [Name] -> [Name] -> Lvl -> Val Ix -> Val Ix -> Checker (Variant e) ()
    conv' ns ns' lvl (VRigid x sp) (VRigid x' sp')
      | x == x' = convSp ns ns' lvl sp sp'
    conv' _ _ _ (VU s) (VU s')
      | s == s' = pure ()
      | otherwise = throw (ConversionBetweenUniverses pos)
    conv' ns ns' lvl (VLambda x t) (VLambda x' t') =
      conv' (ns :> x) (ns' :> x') (lvl + 1) (t (VVar lvl)) (t' (VVar lvl))
    conv' ns ns' lvl (VLambda x t) t' =
      conv' (ns :> x) (ns' :> x) (lvl + 1) (t (VVar lvl)) (t' $$ VApp (VVar lvl))
    conv' ns ns' lvl t (VLambda x' t') =
      conv' (ns :> x') (ns' :> x') (lvl + 1) (t $$ VApp (VVar lvl)) (t' (VVar lvl))
    conv' ns ns' lvl (VPi s x a b) (VPi s' x' a' b')
      | s == s' = do
          conv' ns ns' lvl a a'
          conv' (ns :> x) (ns' :> x') (lvl + 1) (b (VVar lvl)) (b' (VVar lvl))
    conv' _ _ _ VZero VZero = pure ()
    conv' ns ns' lvl (VSucc n) (VSucc n') = conv' ns ns' lvl n n'
    conv' _ _ _ VNat VNat = pure ()
    conv' ns ns' lvl (VExists x a b) (VExists x' a' b') = do
      conv' ns ns' lvl a a'
      conv' (ns :> x) (ns' :> x') (lvl + 1) (b (VVar lvl)) (b' (VVar lvl))
    -- Both terms have the same type (by invariant), so [a ≡ a'], and [t] and [t'] are
    -- both of type [⊥], thus also convertible.
    conv' _ _ _ (VAbort {}) (VAbort {}) = pure ()
    conv' _ _ _ VEmpty VEmpty = pure ()
    -- Proof irrelevant, so always convertible
    conv' _ _ _ VOne _ = pure ()
    conv' _ _ _ _ VOne = pure ()
    conv' _ _ _ VUnit VUnit = pure ()
    conv' ns ns' lvl (VEq t a u) (VEq t' a' u') = do
      conv' ns ns' lvl t t'
      conv' ns ns' lvl a a'
      conv' ns ns' lvl u u'
    conv' ns ns' lvl (VCast a b t) (VCast a' b' t') = do
      conv' ns ns' lvl a a'
      conv' ns ns' lvl b b'
      -- [e ≡ e'] follows from proof irrelevance, given [a ≡ a'] and [b ≡ b']
      conv' ns ns' lvl t t'
    conv' ns ns' lvl (VPair t u) (VPair t' u') = do
      conv' ns ns' lvl t t'
      conv' ns ns' lvl u u'
    conv' ns ns' lvl (VPair t u) t' = do
      conv' ns ns' lvl t (t' $$ VFst)
      conv' ns ns' lvl u (t' $$ VSnd)
    conv' ns ns' lvl t (VPair t' u') = do
      conv' ns ns' lvl (t $$ VFst) t'
      conv' ns ns' lvl (t $$ VSnd) u'
    conv' ns ns' lvl (VSigma x a b) (VSigma x' a' b') = do
      conv' ns ns' lvl a a'
      conv' (ns :> x) (ns' :> x') (lvl + 1) (b (VVar lvl)) (b' (VVar lvl))
    conv' ns ns' lvl (VQuotient a x y r) (VQuotient a' x' y' r') = do
      conv' ns ns' lvl a a'
      conv'
        (ns :> x :> y)
        (ns' :> x' :> y')
        (lvl + 2)
        (r (VVar lvl) (VVar (lvl + 1)))
        (r' (VVar lvl) (VVar (lvl + 1)))
    conv' ns ns' lvl (VQProj t) (VQProj t') = conv' ns ns' lvl t t'
    conv' ns ns' lvl (VIdRefl t) (VIdRefl t') = conv' ns ns' lvl t t'
    conv' _ _ _ VIdPath VIdPath = pure ()
    conv' ns ns' lvl (VId a t u) (VId a' t' u') = do
      conv' ns ns' lvl a a'
      conv' ns ns' lvl t t'
      conv' ns ns' lvl u u'
    conv' ns ns' lvl a b =
      let aTS = TS (prettyPrintTerm ns (quote lvl a))
          bTS = TS (prettyPrintTerm ns' (quote lvl b))
       in throw (ConversionFailure aTS bTS pos)

ppVal :: Context -> Val Ix -> TermString
ppVal gamma v = TS (prettyPrintTerm (names gamma) (quote (lvl gamma) v))

ppTerm :: Context -> Term Ix -> TermString
ppTerm gamma = TS . prettyPrintTerm (names gamma)

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
    find (types :> (x, (s, a))) x'
      | x == x' = pure (0, a, s)
      | otherwise = do
          (i, s, a) <- find types x'
          pure (i + 1, s, a)

infer
  :: ( e `CouldBe` InferenceError
     , e `CouldBe` CheckError
     , e `CouldBe` ConversionError
     )
  => Context
  -> Raw
  -> Checker (Variant e) (Term Ix, VTy Ix, Relevance)
infer gamma (R pos (VarF x)) = inferVar pos (types gamma) x
infer _ (R _ (UF s)) = pure (U s, VU Relevant, Relevant)
infer gamma (R _ (AppF t@(R fnPos _) u)) = do
  (t, tty, s) <- infer gamma t
  case tty of
    VPi _ _ a b -> do
      u <- check gamma u a
      let vu = eval (env gamma) u
      pure (App t u, b vu, s)
    _ -> throw (ApplicationHead (ppVal gamma tty) fnPos)
infer gamma (R _ (PiF s x a b)) = do
  a <- check gamma a (VU s)
  let va = eval (env gamma) a
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
  let a0 = eval (env gamma :> VZero) a
  t0 <- check gamma t0 a0
  let vx = VVar (lvl gamma)
  let an = eval (env gamma :> vx) a
      aSn = eval (env gamma :> VSucc vx) a
  ts <- check (gamma & bindR x VNat & bind ih s an) ts aSn
  -- In general, argument to inductor should be inferred, but can be checked
  -- in simple case of Nat
  n <- check gamma n VNat
  let vn = eval (env gamma) n
  pure (NElim z a t0 x ih ts n, eval (env gamma :> vn) a, s)
infer _ (R _ NatF) = pure (Nat, VU Relevant, Relevant)
infer gamma (R _ (FstF () t@(R pos _))) = do
  (t, tty, _) <- infer gamma t
  case tty of
    VExists _ a _ -> pure (PropFst t, a, Irrelevant)
    VSigma _ a _ -> pure (Fst t, a, Relevant)
    _ -> throw (FstProjectionHead (ppVal gamma tty) pos)
infer gamma (R _ (SndF () t@(R pos _))) = do
  (t, tty, _) <- infer gamma t
  case tty of
    VExists _ _ b -> pure (PropSnd t, b VOne, Irrelevant)
    VSigma _ _ b ->
      let vt = eval (env gamma) t
       in pure (Snd t, b (vt $$ VFst), Relevant)
    _ -> throw (SndProjectionHead (ppVal gamma tty) pos)
infer gamma (R _ (ExistsF x a b)) = do
  a <- check gamma a (VU Irrelevant)
  let va = eval (env gamma) a
  b <- check (bindP x va gamma) b (VU Irrelevant)
  pure (Exists x a b, VU Irrelevant, Relevant)
infer gamma (R _ (AbortF a t)) = do
  (a, s) <- checkType gamma a
  let va = eval (env gamma) a
  t <- check gamma t VEmpty
  pure (Abort a t, va, s)
infer _ (R _ EmptyF) = pure (Empty, VU Irrelevant, Relevant)
infer _ (R _ OneF) = pure (One, VUnit, Irrelevant)
infer _ (R _ UnitF) = pure (Unit, VU Irrelevant, Relevant)
infer gamma (R _ (EqF t a u)) = do
  a <- check gamma a (VU Relevant)
  let va = eval (env gamma) a
  t <- check gamma t va
  u <- check gamma u va
  pure (Eq t a u, VU Irrelevant, Relevant)
infer gamma (R _ (ReflF t@(R pos _))) = do
  (t, a, s) <- infer gamma t
  let vt = eval (env gamma) t
  when (s == Irrelevant) (throw (ReflIrrelevant (ppVal gamma a) pos))
  pure (Refl t, eqReduce vt a vt, Irrelevant)
infer gamma (R _ (TranspF t@(R pos _) x pf b u t' e)) = do
  (t, va, s) <- infer gamma t
  when (s == Irrelevant) (throw (TranspIrrelevant (ppVal gamma va) pos))
  t' <- check gamma t' va
  let vt = eval (env gamma) t
      vt' = eval (env gamma) t'
  let vx = VVar (lvl gamma)
      t_eq_x = eqReduce vt va vx
  b <- check (gamma & bindR x va & bindP pf t_eq_x) b (VU Irrelevant)
  let b_t_refl = eval (env gamma :> vt :> VOne) b
  u <- check gamma u b_t_refl
  e <- check gamma e (eqReduce vt va vt')
  let b_t'_e = eval (env gamma :> vt' :> VOne) b
  pure (Transp t x pf b u t' e, b_t'_e, Irrelevant)
infer gamma (R _ (CastF a@(R aPos _) b@(R bPos _) e t)) = do
  (a, s) <- checkType gamma a
  (b, s') <- checkType gamma b
  let va = eval (env gamma) a
      vb = eval (env gamma) b
  when (s /= s') (throw (CastBetweenUniverses s aPos s' bPos))
  e <- check gamma e (eqReduce va (VU s) vb)
  t <- check gamma t va
  pure (Cast a b e t, vb, s)
infer gamma (R _ (CastReflF a t)) = do
  a <- check gamma a (VU Relevant)
  let va = eval (env gamma) a
  t <- check gamma t va
  let vt = eval (env gamma) t
      cast_a_a_t = cast va va vt
      t_eq_cast_a_a_t = eqReduce vt va cast_a_a_t
  pure (CastRefl a t, t_eq_cast_a_a_t, Irrelevant)
infer gamma (R _ (SigmaF x a b)) = do
  a <- check gamma a (VU Relevant)
  let va = eval (env gamma) a
  b <- check (bindR x va gamma) b (VU Relevant)
  pure (Sigma x a b, VU Relevant, Relevant)
infer gamma (R _ (QuotientF a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)) = do
  a <- check gamma a (VU Relevant)
  let va = eval (env gamma) a
  r <- check (gamma & bindR x va & bindR y va) r (VU Irrelevant)
  let vx = VVar (lvl gamma)
      vy = VVar (lvl gamma + 1)
      vz = VVar (lvl gamma + 2)
  let vrxx = eval (env gamma :> vx :> vx) r
  rr <- check (gamma & bindR x va) rr vrxx
  let vrxy = eval (env gamma :> vx :> vy) r
      vryx = eval (env gamma :> vy :> vx) r
  rs <- check (gamma & bindR sx va & bindR sy va & bindP sxy vrxy) rs vryx
  let vryz = eval (env gamma :> vy :> vz) r
      vrxz = eval (env gamma :> vx :> vz) r
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
    VQuotient a _ _ r -> do
      (b, s) <- checkType (gamma & bindR z uty) b
      let vx = VVar (lvl gamma)
          vy = VVar (lvl gamma + 1)
      let b_pix = eval (env gamma :> VQProj vx) b
          b_piy = eval (env gamma :> VQProj vy) b
      tpi <- check (gamma & bindR x a) tpi b_pix
      let tpi_x = eval (env gamma :> vx) tpi
          tpi_y = eval (env gamma :> vy) tpi
          cast_b_piy_b_pix = cast b_piy b_pix tpi_y
          tpi_x_eq_tpi_y = eqReduce tpi_x b_pix cast_b_piy_b_pix
      p <-
        check
          (gamma & bindR px a & bindR py a & bindP pe (r vx vy))
          p
          tpi_x_eq_tpi_y
      let vu = eval (env gamma) u
          bu = eval (env gamma :> vu) b
      pure (QElim z b x tpi px py pe p u, bu, s)
    _ -> throw (QuotientHead (ppVal gamma uty) pos)
infer gamma (R _ (IdReflF t@(R pos _))) = do
  (t, a, s) <- infer gamma t
  when (s == Irrelevant) (throw (IdReflIrrelevant (ppVal gamma a) pos))
  let vt = eval (env gamma) t
  pure (IdRefl t, VId a vt vt, Relevant)
infer gamma (R _ (JF a t x pf b u t' e)) = do
  a <- check gamma a (VU Relevant)
  let va = eval (env gamma) a
  t <- check gamma t va
  let vt = eval (env gamma) t
      vx = VVar (lvl gamma)
  (b, s) <- checkType (gamma & bindR x va & bindR pf (VId va vt vx)) b
  let b_t_idrefl_t = eval (env gamma :> vt :> VIdRefl vt) b
  u <- check gamma u b_t_idrefl_t
  t' <- check gamma t' va
  let vt' = eval (env gamma) t'
  e <- check gamma e (VId va vt vt')
  let ve = eval (env gamma) e
  let b_t'_e = eval (env gamma :> vt' :> ve) b
  pure (J a t x pf b u t' e, b_t'_e, s)
infer gamma (R _ (IdF a t u)) = do
  a <- check gamma a (VU Relevant)
  let va = eval (env gamma) a
  t <- check gamma t va
  u <- check gamma u va
  pure (Id a t u, VU Relevant, Relevant)
infer gamma (R _ (LetF x a t u)) = do
  (a, s) <- checkType gamma a
  let va = eval (env gamma) a
  t <- check gamma t va
  let vt = eval (env gamma) t
  (u, uty, s') <- infer (define x vt s va gamma) u
  pure (Let x a t u, uty, s')
infer gamma (R _ (AnnotationF t a)) = do
  (a, s) <- checkType gamma a
  let va = eval (env gamma) a
  t <- check gamma t va
  pure (Annotation t a, va, s)
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
    _ -> throw (CheckType (ppVal gamma tty) pos)

check
  :: ( e `CouldBe` CheckError
     , e `CouldBe` InferenceError
     , e `CouldBe` ConversionError
     )
  => Context
  -> Raw
  -> VTy Ix
  -> Checker (Variant e) (Term Ix)
check gamma (R _ (LambdaF x t)) (VPi s _ a b) = do
  let b' = b (VVar (lvl gamma))
  t <- check (bind x s a gamma) t b'
  pure (Lambda x t)
check gamma (R pos (LambdaF {})) tty = throw (CheckLambda (ppVal gamma tty) pos)
check gamma (R _ (PropPairF t u)) (VExists _ a b) = do
  t <- check gamma t a
  u <- check gamma u (b VOne)
  pure (PropPair t u)
check gamma (R pos (PropPairF {})) tty =
  throw (CheckPropPair (ppVal gamma tty) pos)
check gamma (R _ (PairF t u)) (VSigma _ a b) = do
  t <- check gamma t a
  let vt = eval (env gamma) t
  u <- check gamma u (b vt)
  pure (Pair t u)
check gamma (R pos (PairF {})) tty = throw (CheckPair (ppVal gamma tty) pos)
check gamma (R _ (QProjF t)) (VQuotient a _ _ _) =
  -- Inductively, VQuotient contains an equivalent relation; no need to check that
  do
    t <- check gamma t a
    pure (QProj t)
check gamma (R pos (QProjF {})) tty =
  throw (CheckQuotientProj (ppVal gamma tty) pos)
check gamma (R _ (IdPathF e)) (VId a t u) = do
  e <- check gamma e (eqReduce t a u)
  pure (IdPath e)
check gamma (R pos (IdPathF {})) tty = throw (CheckIdPath (ppVal gamma tty) pos)
check gamma (R _ (LetF x a t u)) uty = do
  (a, s) <- checkType gamma a
  let va = eval (env gamma) a
  t <- check gamma t va
  let vt = eval (env gamma) t
  u <- check (define x vt s va gamma) u uty
  pure (Let x a t u)
check gamma t@(R pos _) tty = do
  (t, tty', _) <- infer gamma t
  conv pos (names gamma) (lvl gamma) tty tty'
  pure t

-- TODO: Points to discuss:
-- 1. NbE evaluating irrelevant terms - consider relevance-driven evaluation?
--    (Probably implies tagged apps)
-- 2. CastRefl check/infer?
--    If infer: what do we infer for [e]? (perhaps [refl t]).
--    If check: do we check that each [t] and each [A] is convertible?
-- 3. Naive implementation used WHNF bidirectional conversion checking
--    (https://www.cse.chalmers.se/~abela/types10.pdf), but presumably lots of the
--    complexity vanishes as everything is already a semantic value. Alternatively, is
--    there any reason to avoid the NbE type conversion checking used by Andras Kovacs?
-- 4. Constructing semantic vals in checking which aren't "normal forms"
