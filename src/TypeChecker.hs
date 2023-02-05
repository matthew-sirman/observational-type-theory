module TypeChecker where

import Data.Function ((&))
import Control.Monad.Except
import Error.Diagnose
import Syntax

type Checker a = Except (Report String) a

type Types = [(Name, (Relevance, VTy Ix))]

data Context = Context
  { env :: Env Ix,
    types :: Types,
    lvl :: Lvl
  }

names :: Context -> [Name]
names = map fst . types

createError :: String -> [(Position, String)] -> Checker a
createError message context =
  throwError (Err Nothing message [(pos, This msg) | (pos, msg) <- context] [])

emptyContext :: Context
emptyContext = Context { env = [], types = [], lvl = 0 }

eqReduce :: Val Ix -> VTy Ix -> Val Ix -> Val Ix
eqReduce vt va vu = eqReduceType va
  where
    -- Initially driven just by the type
    eqReduceType :: VTy Ix -> Val Ix
    -- Rule Eq-Fun
    eqReduceType (VPi s x a b) =
      let fx_eq_gx vx = eqReduce (vt $$ vx) (b vx) (vu $$ vx)
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

    -- Then driven by terms and type
    eqReduceAll :: Val Ix -> VTy Ix -> Val Ix -> Val Ix
    -- Rules Eq-Univ and Eq-Univ-≠
    eqReduceAll vt (VU Relevant) vu
      | not (headEq vt vu) = VEmpty
    eqReduceAll VNat (VU Relevant) VNat = VUnit
    eqReduceAll (VU s) (VU Relevant) (VU s')
      | s == s' = VUnit
      | otherwise = VEmpty
    -- Rule Eq-Π
    eqReduceAll (VPi s _ a b) (VU Relevant) (VPi s' x' a' b')
      | s == s' =
        let a_eq_a' = eqReduce a (VU Relevant) a'
            b_eq_b' _ = VPi s x' a' (\v -> eqReduce (b (cast a' a v)) (VU Relevant) (b' v))
         in VExists "e" a_eq_a' b_eq_b'
    -- Rule Eq-Σ
    eqReduceAll (VSigma _ a b) (VU Relevant) (VSigma x' a' b') =
      let a_eq_a' = eqReduce a (VU Relevant) a'
          b_eq_b' v = eqReduce (b (cast a' a v)) (VU Relevant) (b' v)
      in VExists "e" a_eq_a' (\_ -> VPi Relevant x' a' b_eq_b')
    -- Rule Eq-Quotient
    eqReduceAll (VQuotient a x y r) (VU Relevant) (VQuotient a' _ _ r') =
      let a_eq_a' = eqReduce a (VU Relevant) a'
          rxy_eq_rx'y' vx vy = eqReduce (r vx vy) (VU Irrelevant) (r' (cast a a' vx) (cast a a' vy))
      in VExists "e" a_eq_a' (\_ -> VPi Relevant x a (VPi Relevant y a . rxy_eq_rx'y'))
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

    headEq :: VTy Ix -> VTy Ix -> Bool
    headEq VNat VNat = True
    headEq (VPi {}) (VPi {}) = True
    headEq (VU {}) (VU {}) = True
    headEq (VSigma {}) (VSigma {}) = True
    headEq (VQuotient {}) (VQuotient {}) = True
    headEq _ _ = False

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
   in VLambda x' (\va' ->
                    let a = cast_a'_a va'
                    in cast (b a) (b' va') (f $$ a))
cast (VSigma _ a b) (VSigma _ a' b') (VPair t u) =
  let t' = cast a a' t
      u' = cast (b t) (b' t') u
  in VPair t' u'
cast (VQuotient a _ _ _) (VQuotient a' _ _ _) (VQProj t) = VQProj (cast a a' t)
cast (VId {}) (VId {}) (VIdRefl _) = VIdPath
cast (VId {}) (VId {}) VIdPath = VIdPath
cast a b t = VCast a b t

eval :: Env Ix -> Term Ix -> Val Ix
eval env (Var (Ix x)) = env !! x
eval _ (U s) = VU s
eval env (Lambda x e) = VLambda x (\vx -> eval (env :> vx) e)
eval env (App t u) = eval env t $$ eval env u
eval env (Pi s x a b) = VPi s x (eval env a) (\vx -> eval (env :> vx) b)
eval _ Zero = VZero
eval env (Succ n) = VSucc (eval env n)
eval env (NElim z a t0 x ih ts n) = recurse (eval env n)
  where
    recurse :: Val Ix -> Val Ix
    recurse VZero = eval env t0
    recurse (VSucc n) = eval (env :> n :> recurse n) ts
    recurse ne = VNElim z (\vz -> eval (env :> vz) a) (eval env t0) x ih (\vx vih -> eval (env :> vx :> vih) ts) ne
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
eval env (Fst p) =
  case eval env p of
    VPair t _ -> t
    p -> VFst p
eval env (Snd p) =
  case eval env p of
    VPair _ u -> u
    p -> VSnd p
eval env (Sigma x a b) = VSigma x (eval env a) (\vx -> eval (env :> vx) b)
eval env (Quotient a x y r _ _ _ _ _ _ _ _ _ _ _ _) =
  VQuotient (eval env a) x y (\vx vy -> eval (env :> vx :> vy) r)
eval env (QProj t) = VQProj (eval env t)
eval env (QElim z b x tpi _ _ _ _ u) =
  case eval env u of
    VQProj t -> eval (env :> t) tpi
    u -> VQElim z (\vz -> eval (env :> vz) b) x (\vx -> eval (env :> vx) tpi) u
eval env (IdRefl t) = VIdRefl (eval env t)
eval _ (IdPath _) = VIdPath
eval env (J a t x pf b u t' e) =
  case ve of
    VIdRefl e -> eval (env :> e :> VIdRefl e) b
    VIdPath ->
      let vt = eval env t
          vt' = eval env t'
          b_t_idrefl_t = eval (env :> vt :> VIdRefl vt) b
          b_t'_idpath_e = eval (env :> vt' :> VIdPath) b
          vu = eval env u
      in cast b_t_idrefl_t b_t'_idpath_e vu
    _ -> VJ va vt x pf (\vx vpf -> eval (env :> vx :> vpf) b) vu vt' ve
  where
    va, vt, vu, vt', ve :: Val Ix
    va = eval env a
    vt = eval env t
    vu = eval env u
    vt' = eval env t'
    ve = eval env e
eval env (Id a t u) = VId (eval env a) (eval env t) (eval env u)
eval env (Let _ _ t u) =
  let vt = eval env t
   in eval (env :> vt) u
eval env (Annotation t _) = eval env t

quote :: Lvl -> Val Ix -> Term Ix
quote (Lvl lvl) (VVar (Lvl x)) = Var (Ix (lvl - x - 1))
quote _ (VU s) = U s
quote lvl (VLambda x t) = Lambda x (quote (lvl + 1) (t (VVar lvl)))
quote lvl (VApp t u) = App (quote lvl t) (quote lvl u)
quote lvl (VPi s x a b) = Pi s x (quote lvl a) (quote (lvl + 1) (b (VVar lvl)))
quote _ VZero = Zero
quote lvl (VSucc t) = Succ (quote lvl t)
quote lvl (VNElim z a t0 x ih ts n) = NElim z a' (quote lvl t0) x ih ts' (quote lvl n)
  where
    a', ts' :: Term Ix
    a' = quote (lvl + 1) (a (VVar lvl))
    ts' = quote (lvl + 2) (ts (VVar lvl) (VVar (lvl + 1)))
quote _ VNat = Nat
quote lvl (VExists x a b) = Exists x (quote lvl a) (quote (lvl + 1) (b (VVar lvl)))
quote lvl (VAbort a) = Abort (quote lvl a) One
quote _ VEmpty = Empty
quote _ VOne = One
quote _ VUnit = Unit
quote lvl (VEq t a u) = Eq (quote lvl t) (quote lvl a) (quote lvl u)
quote lvl (VCast a b t) = Cast (quote lvl a) (quote lvl b) One (quote lvl t)
quote lvl (VPair t u) = Pair (quote lvl t) (quote lvl u)
quote lvl (VSigma x a b) = Sigma x (quote lvl a) (quote (lvl + 1) (b (VVar lvl)))
quote lvl (VFst t) = Fst (quote lvl t)
quote lvl (VSnd t) = Snd (quote lvl t)
quote lvl (VQuotient a x y r) =
  Quotient (quote lvl a) x y (quote (lvl + 2) (r (VVar lvl) (VVar (lvl + 1))))
           "_" One
           "_" "_" "_" One
           "_" "_" "_" "_" "_" One
quote lvl (VQProj t) = QProj (quote lvl t)
quote lvl (VQElim z b x tpi u) =
  QElim z (quote (lvl + 1) (b (VVar lvl))) x (quote (lvl + 1) (tpi (VVar lvl)))
          "_" "_" "_" One
          (quote lvl u)
quote lvl (VIdRefl t) = IdRefl (quote lvl t)
quote _ VIdPath = IdPath One
quote lvl (VJ a t x pf b u v e) = J a' t' x pf b' u' v' e'
  where
    a', t', b', u', v', e' :: Term Ix
    a' = quote lvl a
    t' = quote lvl t
    b' = quote (lvl + 2) (b (VVar lvl) (VVar (lvl + 1)))
    u' = quote lvl u
    v' = quote lvl v
    e' = quote lvl e
quote lvl (VId a t u) = Id (quote lvl a) (quote lvl t) (quote lvl u)

infixl 8 $$

($$) :: Val Ix -> Val Ix -> Val Ix
(VLambda _ c) $$ u = c u
VOne $$ _ = VOne
t $$ u = VApp t u

normalForm :: Env Ix -> Term Ix -> Term Ix
normalForm env t = quote (Lvl (length env)) (eval env t)

bind :: Name -> Relevance -> VTy Ix -> Context -> Context
bind x s tty ctx =
  ctx
    { types = types ctx :> (x, (s, tty)),
      lvl = lvl ctx + 1,
      env = env ctx :> VVar (lvl ctx)
    }

bindR, bindP :: Name -> VTy Ix -> Context -> Context
bindR x = bind x Relevant
bindP x = bind x Irrelevant

define :: Name -> Val Ix -> Relevance -> VTy Ix -> Context -> Context
define x t s tty ctx =
  ctx
    { types = types ctx :> (x, (s, tty)),
      lvl = lvl ctx + 1,
      env = env ctx :> t
    }

mapHead :: (a -> a) -> [a] -> [a]
mapHead _ [] = []
mapHead f (x : xs) = f x : xs

conv ::  Position -> [Name] -> Lvl -> Val Ix -> Val Ix -> Checker ()
conv pos names = conv' names names
  where
    conv' :: [Name] -> [Name] -> Lvl -> Val Ix -> Val Ix -> Checker ()
    conv' _ _ _ (VVar x) (VVar x')
      | x == x' = pure ()
    conv' _ _ _ (VU s) (VU s')
      | s == s' = pure ()
      | otherwise = createError "Type conversion failed." [(pos, "Cannot convert between universes.")]
    conv' ns ns' lvl (VLambda x t) (VLambda x' t') =
      conv' (ns :> x) (ns' :> x') (lvl + 1) (t (VVar lvl)) (t' (VVar lvl))
    conv' ns ns' lvl (VLambda x t) t' =
      conv' (ns :> x) (ns' :> x) (lvl + 1) (t (VVar lvl)) (VApp t' (VVar lvl))
    conv' ns ns' lvl t (VLambda x' t') =
      conv' (ns :> x') (ns' :> x') (lvl + 1) (VApp t (VVar lvl)) (t' (VVar lvl))
    conv' ns ns' lvl (VApp t u) (VApp t' u') = do
      conv' ns ns' lvl t t'
      conv' ns ns' lvl u u'
    conv' ns ns' lvl (VPi s x a b) (VPi s' x' a' b')
      | s == s' = do
          conv' ns ns' lvl a a'
          conv' (ns :> x) (ns' :> x') (lvl + 1) (b (VVar lvl)) (b' (VVar lvl))
    conv' _ _ _ VZero VZero = pure ()
    conv' ns ns' lvl (VSucc n) (VSucc n') =
      conv' ns ns' lvl n n'
    conv' ns ns' lvl (VNElim z a t0 x ih ts n) (VNElim z' a' t0' x' ih' ts' n') = do
      conv' (ns :> z) (ns' :> z') (lvl + 1) (a (VVar lvl)) (a' (VVar lvl))
      conv' ns ns' lvl t0 t0'
      conv' (ns :> x :> ih) (ns' :> x' :> ih') (lvl + 2) (ts (VVar lvl) (VVar (lvl + 1))) (ts' (VVar lvl) (VVar (lvl + 1)))
      conv' ns ns' lvl n n'
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
      conv' ns ns' lvl t (VFst t')
      conv' ns ns' lvl u (VSnd t')
    conv' ns ns' lvl t (VPair t' u') = do
      conv' ns ns' lvl (VFst t) t'
      conv' ns ns' lvl (VSnd t) u'
    conv' ns ns' lvl (VFst t) (VFst t') = conv' ns ns' lvl t t'
    conv' ns ns' lvl (VSnd t) (VSnd t') = conv' ns ns' lvl t t'
    conv' ns ns' lvl (VSigma x a b) (VSigma x' a' b') = do
      conv' ns ns' lvl a a'
      conv' (ns :> x) (ns' :> x') (lvl + 1) (b (VVar lvl)) (b' (VVar lvl))
    conv' ns ns' lvl (VQuotient a x y r) (VQuotient a' x' y' r') = do
      conv' ns ns' lvl a a'
      conv' (ns :> x :> y) (ns' :> x' :> y') (lvl + 2) (r (VVar lvl) (VVar (lvl + 1))) (r' (VVar lvl) (VVar (lvl + 1)))
    conv' ns ns' lvl (VQProj t) (VQProj t') = conv' ns ns' lvl t t'
    conv' ns ns' lvl (VQElim z b x tpi u) (VQElim z' b' x' tpi' u') = do
      conv' (ns :> z) (ns' :> z') (lvl + 1) (b (VVar lvl)) (b' (VVar lvl))
      conv' (ns :> x) (ns' :> x') (lvl + 1) (tpi (VVar lvl)) (tpi' (VVar lvl))
      conv' ns ns' lvl u u'
    conv' ns ns' lvl (VIdRefl t) (VIdRefl t') = conv' ns ns' lvl t t'
    conv' _ _ _ VIdPath VIdPath = pure ()
    conv' ns ns' lvl (VJ a t x pf b u v e) (VJ a' t' x' pf' b' u' v' e') = do
      conv' ns ns' lvl a a'
      conv' ns ns' lvl t t'
      conv' (ns :> x :> pf) (ns' :> x' :> pf') (lvl + 2) (b (VVar lvl) (VVar (lvl + 1))) (b' (VVar lvl) (VVar (lvl + 1)))
      conv' ns ns' lvl u u'
      conv' ns ns' lvl v v'
      conv' ns ns' lvl e e'
    conv' ns ns' lvl (VId a t u) (VId a' t' u') = do
      conv' ns ns' lvl a a'
      conv' ns ns' lvl t t'
      conv' ns ns' lvl u u'
    conv' ns ns' lvl a b =
      createError
        "Type conversion failed."
        [(pos, "Failed to convert ["
           ++ prettyPrintTerm ns (quote lvl a)
           ++ " ≡ "
           ++ prettyPrintTerm ns' (quote lvl b)
           ++ "]."
         )]

ppVal :: Context -> Val Ix -> String
ppVal gamma v = prettyPrintTerm (names gamma) (quote (lvl gamma) v)

ppTerm :: Context -> Term Ix -> String
ppTerm gamma = prettyPrintTerm (names gamma)

inferVar :: Position -> Types -> Name -> Checker (Term Ix, VTy Ix, Relevance)
inferVar pos types name = do
  (i, ty, s) <- find types name
  pure (Var i, ty, s)
  where
    find :: Types -> Name -> Checker (Ix, VTy Ix, Relevance)
    find [] name = createError "Variable not in scope." [(pos, "Variable '" ++ name ++ "' is not defined.")]
    find (types :> (x, (s, a))) x'
      | x == x' = pure (0, a, s)
      | otherwise = do
          (i, s, a) <- find types x'
          pure (i + 1, s, a)

infer :: Context -> Raw -> Checker (Term Ix, VTy Ix, Relevance)
infer gamma (R pos (VarF x)) = inferVar pos (types gamma) x
infer _ (R _ (UF s)) = pure (U s, VU Relevant, Relevant)
infer gamma (R _ (AppF t@(R fnPos _) u)) = do
  (t, tty, s) <- infer gamma t
  case tty of
    VPi _ _ a b -> do
      u <- check gamma u a
      let vu = eval (env gamma) u
      pure (App t u, b vu, s)
    _ ->
      let msg = "Expected Π type but found [" ++ ppVal gamma tty ++ "]"
      in createError "Expected Π (Pi) type." [(fnPos, msg)]
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
    _ ->
      let msg  = "Expected ∃ or Σ type, but found ̈[" ++ ppVal gamma tty ++ "]"
      in createError "Expected ∃ (Exists) or Σ type in first projection." [(pos, msg)]
infer gamma (R _ (SndF () t@(R pos _))) = do
  (t, tty, _) <- infer gamma t
  case tty of
    VExists _ _ b -> pure (PropSnd t, b VOne, Irrelevant)
    VSigma _ _ b ->
      let vt = eval (env gamma) t
      in pure (Snd t, b (VFst vt), Relevant)
    _ ->
      let msg  = "Expected ∃ or Σ type, but found ̈[" ++ ppVal gamma tty ++ "]"
      in createError "Expected ∃ (Exists) or Σ type in second projection" [(pos, msg)]
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
  let primaryMsg = "Refl must only witness equalities of relevant types \
                   \ (irrelevant types are trivially convertible)."
      msg = "Term has type [" ++ ppVal gamma a ++ "] which is irrelevant."
  when (s == Irrelevant) (createError primaryMsg [(pos, msg)])
  pure (Refl t, eqReduce vt a vt, Irrelevant)
infer gamma (R _ (TranspF t@(R pos _) x pf b u t' e)) = do
  (t, va, s) <- infer gamma t
  let msg = "Term has type [" ++ ppVal gamma va ++ "] which is irrelevant."
  when (s == Irrelevant) (createError "Can only transport along relevant types." [(pos, msg)])
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
  let aMsg = "Type [" ++ ppTerm gamma a ++ "] has sort [" ++ show s ++ "]."
      bMsg = "Type [" ++ ppTerm gamma b ++ "] has sort [" ++ show s' ++ "]."
  when (s /= s') (createError "Cast types must live in the same universe." [(aPos, aMsg), (bPos, bMsg)])
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
  rt <- check (gamma & bindR tx va & bindR ty va & bindR tz va & bindP txy vrxy & bindP tyz vryz) rt vrxz
  pure (Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt, VU Relevant, Relevant)
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
      p <- check (gamma & bindR px a & bindR py a & bindP pe (r vx vy)) p tpi_x_eq_tpi_y
      let vu = eval (env gamma) u
          bu = eval (env gamma :> vu) b
      pure (QElim z b x tpi px py pe p u, bu, s)
    _ ->
      let msg  = "Expected Quotient (A/R) type, but found ̈[" ++ ppVal gamma uty ++ "]"
      in createError "Expected Quotient type in quotient eliminator" [(pos, msg)]
infer gamma (R _ (IdReflF t@(R pos _))) = do
  (t, a, s) <- infer gamma t
  when (s == Irrelevant) (createError "Can only form inductive equality type over relevant types." [(pos, "Expected relevant type.")])
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
infer _ (R pos _) =
  let msg = "Could not infer type for term."
  in createError "Type inference failed." [(pos, msg)]

checkType :: Context -> Raw -> Checker (Term Ix, Relevance)
checkType gamma t@(R pos _) = do
  (t, tty, _) <- infer gamma t
  case tty of
    VU s -> pure (t, s)
    _ ->
      let msg = "Term has type [" ++ ppVal gamma tty ++ "]; expected a universe sort."
      in createError "Expected type, but found term." [(pos, msg)]

check :: Context -> Raw -> VTy Ix -> Checker (Term Ix)
check gamma (R _ (LambdaF x t)) (VPi s _ a b) = do
  let b' = b (VVar (lvl gamma))
  t <- check (bind x s a gamma) t b'
  pure (Lambda x t)
check gamma (R pos (LambdaF {})) tty =
  let msg = "Checking λ-expression against type [" ++ ppVal gamma tty ++ "] failed (expected Π type)."
  in createError "λ-expression type checking failed." [(pos, msg)]
check gamma (R _ (PropPairF t u)) (VExists _ a b) = do
  t <- check gamma t a
  u <- check gamma u (b VOne)
  pure (PropPair t u)
check gamma (R pos (PropPairF {})) tty =
  let msg = "Checking propositional pair against type [" ++ ppVal gamma tty ++ "] failed (expected ∃ type)."
  in createError "Propositional pair type checking failed." [(pos, msg)]
check gamma (R _ (PairF t u)) (VSigma _ a b) = do
  t <- check gamma t a
  let vt = eval (env gamma) t
  u <- check gamma u (b vt)
  pure (Pair t u)
check gamma (R pos (PairF {})) tty =
  let msg = "Checking pair against type [" ++ ppVal gamma tty ++ "] failed (expected Σ type)."
  in createError "Pair type checking failed." [(pos, msg)]
check gamma (R _ (QProjF t)) (VQuotient a _ _ _) = do
  -- Inductively, VQuotient contains an equivalent relation; no need to check that
  t <- check gamma t a
  pure (QProj t)
check gamma (R pos (QProjF {})) tty =
  let msg = "Checking quotient projection against type [" ++ ppVal gamma tty ++ "] failed (expected Quotient (A/R) type)."
  in createError "Quotient projection type checking failed." [(pos, msg)]
check gamma (R _ (IdPathF e)) (VId a t u) = do
  e <- check gamma e (eqReduce t a u)
  pure (IdPath e)
check gamma (R pos (IdPathF {})) tty =
  let msg = "Checking Idpath argument against type [" ++ ppVal gamma tty ++ "] failed (expected inductive identity type Id(A, t, u))."
  in createError "Idpath type checking failed." [(pos, msg)]
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
