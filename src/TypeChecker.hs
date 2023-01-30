module TypeChecker where

import Control.Monad.Except
import Error.Diagnose
import Syntax

import Debug.Trace

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
    -- Other cases require matching on [t] and [u]
    eqReduceType va = eqReduceAll vt va vu

    -- Then driven by terms and type
    eqReduceAll :: Val Ix -> VTy Ix -> Val Ix -> Val Ix
    -- Rules Eq-Univ and Eq-Univ-≠
    eqReduceAll VNat (VU Relevant) VNat = VUnit
    eqReduceAll (VU s) (VU Relevant) (VU s')
      | s == s' = VUnit
      | otherwise = VEmpty
    eqReduceAll VNat (VU Relevant) (VPi {}) = VEmpty
    eqReduceAll VNat (VU Relevant) (VU {}) = VEmpty
    eqReduceAll (VPi {}) (VU Relevant) VNat = VEmpty
    eqReduceAll (VPi {}) (VU Relevant) (VU {}) = VEmpty
    eqReduceAll (VU {}) (VU Relevant) VNat = VEmpty
    eqReduceAll (VU {}) (VU Relevant) (VPi {}) = VEmpty
    -- Rule Eq-Π
    eqReduceAll (VPi s _ a b) (VU Relevant) (VPi s' x' a' b')
      | s == s' =
        let a'_eq_a = VEq a' (VU Relevant) a
            cast_a'_a = cast a' a
            b_eq_b' e = VPi s x' a' (\v -> VEq (b (cast_a'_a e v)) (VU Relevant) (b' v))
         in VExists "e" a'_eq_a b_eq_b'
    -- Rule Eq-Zero
    eqReduceAll VZero VNat VZero = VUnit
    -- Rule Eq-Zero-Succ
    eqReduceAll VZero VNat (VSucc _) = VEmpty
    -- Rule Eq-Succ-Zero
    eqReduceAll (VSucc _) VNat VZero = VEmpty
    -- Rule Eq-Succ
    eqReduceAll (VSucc m) VNat (VSucc n) = eqReduceAll m VNat n
    -- No reduction rule
    eqReduceAll t a u = VEq t a u

cast :: VTy Ix -> VTy Ix -> Val Ix -> Val Ix -> Val Ix
-- Rule Cast-Zero
cast VNat VNat _ VZero = VZero
-- Rule Cast-Succ
cast VNat VNat e (VSucc n) = VSucc (cast VNat VNat e n)
-- Rule Cast-Univ
cast (VU s) (VU s') _ a
  | s == s' = a
-- Rule Cast-Pi
cast (VPi _ _ a b) (VPi _ x' a' b') e f =
  let cast_a'_a = cast a' a (VFst e)
   in VLambda x' (\va' ->
                    let a = cast_a'_a va'
                    in cast (b a) (b' va') (VSnd e) (f $$ a))
cast a b e t = VCast a b e t

eval :: Env Ix -> Term Ix -> Val Ix
eval env (Var (Ix x)) = env !! x
eval _ (U s) = VU s
eval env (Lambda x e) = VLambda x (\vx -> eval (vx : env) e)
eval env (App t u) = eval env t $$ eval env u
eval env (Pi s x a b) = VPi s x (eval env a) (\vx -> eval (vx : env) b)
eval _ Zero = VZero
eval env (Succ n) = VSucc (eval env n)
eval env (NElim z p t0 x ih ts n) = recurse (eval env n)
  where
    recurse :: Val Ix -> Val Ix
    recurse VZero = eval env t0
    recurse (VSucc n) = eval (recurse n : n : env) ts
    recurse ne = VNElim z (\vz -> eval (vz : env) p) (eval env t0) x ih (\vx vih -> eval (vih : vx : env) ts) ne
eval _ Nat = VNat
eval env (Pair t u) = VPair (eval env t) (eval env u)
eval env (Fst t) = VFst (eval env t)
eval env (Snd t) = VSnd (eval env t)
eval env (Exists x a b) = VExists x (eval env a) (\v -> eval (v : env) b)
eval env (Abort a t) = VAbort (eval env a) (eval env t)
eval _ Empty = VEmpty
eval _ One = VOne
eval _ Unit = VUnit
eval env (Eq t a u) = eqReduce (eval env t) (eval env a) (eval env u)
eval env (Refl t) = VRefl (eval env t)
eval env (Transp t x pf b u t' e) =
  VTransp (eval env t) x pf (\vx vpf -> eval (vpf : vx: env) b) (eval env u) (eval env t') (eval env e)
eval env (Cast a b e t) = cast (eval env a) (eval env b) (eval env e) (eval env t)
eval env (CastRefl a t) = VCastRefl (eval env a) (eval env t)
eval env (Let _ _ t u) =
  let vt = eval env t
   in eval (vt : env) u
eval env (Annotation t _) = eval env t

quote :: Lvl -> Val Ix -> Term Ix
quote (Lvl lvl) (VVar (Lvl x)) = Var (Ix (lvl - x - 1))
quote _ (VU s) = U s
quote lvl (VLambda x t) = Lambda x (quote (lvl + 1) (t (VVar lvl)))
quote lvl (VApp t u) = App (quote lvl t) (quote lvl u)
quote lvl (VPi s x a b) = Pi s x (quote lvl a) (quote (lvl + 1) (b (VVar lvl)))
quote _ VZero = Zero
quote lvl (VSucc t) = Succ (quote lvl t)
quote lvl (VNElim z p t0 x ih ts n) = NElim z p' (quote lvl t0) x ih ts' (quote lvl n)
  where
    p', ts' :: Term Ix
    p' = quote (lvl + 1) (p (VVar lvl))
    ts' = quote (lvl + 2) (ts (VVar lvl) (VVar (lvl + 1)))
quote _ VNat = Nat
quote lvl (VPair t u) = Pair (quote lvl t) (quote lvl u)
quote lvl (VFst t) = Fst (quote lvl t)
quote lvl (VSnd t) = Snd (quote lvl t)
quote lvl (VExists x a b) = Exists x (quote lvl a) (quote (lvl + 1) (b (VVar lvl)))
quote lvl (VAbort a t) = Abort (quote lvl a) (quote lvl t)
quote _ VEmpty = Empty
quote _ VOne = One
quote _ VUnit = Unit
quote lvl (VEq t a u) = Eq (quote lvl t) (quote lvl a) (quote lvl u)
quote lvl (VRefl t) = Refl (quote lvl t)
quote lvl (VTransp t x pf b u t' e) =
  Transp (quote lvl t) x pf b' (quote lvl u) (quote lvl t') (quote lvl e)
  where
    b' :: Term Ix
    b' = quote (lvl + 2) (b (VVar lvl) (VVar (lvl + 1)))
quote lvl (VCast a b e t) = Cast (quote lvl a) (quote lvl b) (quote lvl e) (quote lvl t)
quote lvl (VCastRefl a t) = CastRefl (quote lvl a) (quote lvl t)

infixl 8 $$

($$) :: Val Ix -> Val Ix -> Val Ix
(VLambda _ c) $$ u = c u
t $$ u = VApp t u

normalForm :: Env Ix -> Term Ix -> Term Ix
normalForm env t = quote (Lvl (length env)) (eval env t)

inferVar :: Position -> Types -> Name -> Checker (Term Ix, Relevance, VTy Ix)
inferVar pos types name = do
  (i, s, ty) <- find types name
  pure (Var i, s, ty)
  where
    find :: Types -> Name -> Checker (Ix, Relevance, VTy Ix)
    find [] name = createError "Variable not in scope." [(pos, "Variable '" ++ name ++ "' is not defined.")]
    find ((x, (s, a)) : types) x'
      | x == x' = pure (0, s, a)
      | otherwise = do
          (i, s, a) <- find types x'
          pure (i + 1, s, a)

bind :: Name -> Relevance -> VTy Ix -> Context -> Context
bind x s tty ctx =
  ctx
    { types = (x, (s, tty)) : types ctx,
      lvl = 1 + lvl ctx,
      env = VVar (lvl ctx) : env ctx
    }

define :: Name -> Val Ix -> Relevance -> VTy Ix -> Context -> Context
define x t s tty ctx =
  ctx
    { types = (x, (s, tty)) : types ctx,
      lvl = 1 + lvl ctx,
      env = t : env ctx
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
      conv' (x : ns) (x' : ns') (lvl + 1) (t (VVar lvl)) (t' (VVar lvl))
    conv' ns ns' lvl (VLambda x t) t' =
      conv' (x : ns) (x : ns') (lvl + 1) (t (VVar lvl)) (VApp t' (VVar lvl))
    conv' ns ns' lvl t (VLambda x' t') =
      conv' (x' : ns) (x' : ns') (lvl + 1) (VApp t (VVar lvl)) (t' (VVar lvl))
    conv' ns ns' lvl (VApp t u) (VApp t' u') = do
      conv' ns ns' lvl t t'
      conv' ns ns' lvl u u'
    conv' ns ns' lvl (VPi s x a b) (VPi s' x' a' b')
      | s == s' = do
          conv' ns ns' lvl a a'
          conv' (x : ns) (x' : ns') (lvl + 1) (b (VVar lvl)) (b' (VVar lvl))
    conv' _ _ _ VZero VZero = pure ()
    conv' ns ns' lvl (VSucc n) (VSucc n') =
      conv' ns ns' lvl n n'
    conv' ns ns' lvl (VNElim z p t0 x ih ts n) (VNElim z' p' t0' x' ih' ts' n') = do
      conv' (z : ns) (z' : ns') (lvl + 1) (p (VVar lvl)) (p' (VVar lvl))
      conv' ns ns' lvl t0 t0'
      conv' (ih : x : ns) (ih' : x' : ns) (lvl + 2) (ts (VVar lvl) (VVar (lvl + 1))) (ts' (VVar lvl) (VVar (lvl + 1)))
      conv' ns ns' lvl n n'
    conv' _ _ _ VNat VNat = pure ()
    -- Proof irrelevant, so always convertible
    conv' _ _ _ (VFst _) _ = pure ()
    conv' _ _ _ _ (VFst _) = pure ()
    conv' _ _ _ (VSnd _) _ = pure ()
    conv' _ _ _ _ (VSnd _) = pure ()
    conv' ns ns' lvl (VExists x a b) (VExists x' a' b') = do
      conv' ns ns' lvl a a'
      conv' (x : ns) (x' : ns') (lvl + 1) (b (VVar lvl)) (b' (VVar lvl))
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
    -- Proof irrelevant, so always convertible
    conv' _ _ _ (VRefl _) _ = pure ()
    conv' _ _ _ _ (VRefl _) = pure ()
    conv' _ _ _ (VTransp {}) _ = pure ()
    conv' _ _ _ _ (VTransp {}) = pure ()
    conv' ns ns' lvl (VCast a b _ t) (VCast a' b' _ t') = do
      conv' ns ns' lvl a a'
      conv' ns ns' lvl b b'
      -- [e ≡ e'] follows from proof irrelevance, given [a ≡ a'] and [b ≡ b']
      conv' ns ns' lvl t t'
    -- Proof irrelevant, so always convertible
    conv' _ _ _ (VCastRefl {}) _ = pure ()
    conv' _ _ _ _ (VCastRefl {}) = pure ()
    -- TODO: Proper error messages
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

infer :: Context -> Raw -> Checker (Term Ix, Relevance, VTy Ix)
infer gamma (R pos (VarF x)) = inferVar pos (types gamma) x
infer _ (R _ (UF s)) = pure (U s, Relevant, VU Relevant)
infer gamma (R _ (AppF t@(R fnPos _) u)) = do
  (t, s, tty) <- infer gamma t
  case tty of
    VPi _ _ a b -> do
      u <- check gamma u a
      let vu = eval (env gamma) u
      pure (App t u, s, b vu)
    _ ->
      let msg = "Expected Π type but found [" ++ ppVal gamma tty ++ "]"
      in createError "Expected Π (Pi) type." [(fnPos, msg)]
infer gamma (R _ (PiF s x a b)) = do
  a <- check gamma a (VU s)
  let va = eval (env gamma) a
  (b, s') <- checkType (bind x s va gamma) b
  pure (Pi s x a b, Relevant, VU s')
-- In general, constructors must be checked, but the simple case of naturals
-- can be inferred.
infer _ (R _ ZeroF) = pure (Zero, Relevant, VNat)
infer gamma (R _ (SuccF n)) = do
  n <- check gamma n VNat
  pure (Succ n, Relevant, VNat)
infer gamma (R _ (NElimF z p t0 x ih ts n)) = do
  (p, s) <- checkType (bind z Relevant VNat gamma) p
  t0 <- check gamma t0 (eval (VZero : env gamma) p)
  let gamma' = bind x Relevant VNat gamma
      gamma'' = bind ih s (eval (env gamma') p) gamma'
  ts <- check gamma'' ts (eval (mapHead VSucc (env gamma')) p)
  -- In general, argument to inductor should be inferred, but can be checked
  -- in simple case of Nat
  n <- check gamma n VNat
  let vn = eval (env gamma) n
  pure (NElim z p t0 x ih ts n, s, eval (vn : env gamma) p)
infer _ (R _ NatF) = pure (Nat, Relevant, VU Relevant)
infer gamma (R _ (FstF t@(R pos _))) = do
  (t, _, tty) <- infer gamma t
  case tty of
    VExists _ a _ -> pure (Fst t, Irrelevant, a)
    _ ->
      let msg  = "Expected ∃ type, but found ̈[" ++ ppVal gamma tty ++ "]"
      in createError "Expected ∃ (Exists) type in first projection." [(pos, msg)]
infer gamma (R _ (SndF t@(R pos _))) = do
  (t, _, tty) <- infer gamma t
  case tty of
    VExists _ _ b ->
      let vt = eval (env gamma) t
      in pure (Snd t, Irrelevant, b (VFst vt))
    _ ->
      let msg  = "Expected ∃ type, but found ̈[" ++ ppVal gamma tty ++ "]"
      in createError "Expected ∃ (Exists) type in second projection" [(pos, msg)]
infer gamma (R _ (ExistsF x a b)) = do
  a <- check gamma a (VU Irrelevant)
  let va = eval (env gamma) a
  b <- check (bind x Irrelevant va gamma) b (VU Irrelevant)
  pure (Exists x a b, Relevant, VU Irrelevant)
infer gamma (R _ (AbortF a t)) = do
  (a, s) <- checkType gamma a
  let va = eval (env gamma) a
  t <- check gamma t VEmpty
  pure (Abort a t, s, va)
infer _ (R _ EmptyF) = pure (Empty, Relevant, VU Irrelevant)
infer _ (R _ OneF) = pure (One, Irrelevant, VUnit)
infer _ (R _ UnitF) = pure (Unit, Relevant, VU Irrelevant)
infer gamma (R _ (EqF t a u)) = do
  a <- check gamma a (VU Relevant)
  let va = eval (env gamma) a
  t <- check gamma t va
  u <- check gamma u va
  pure (Eq t a u, Relevant, VU Irrelevant)
infer gamma (R _ (ReflF t@(R pos _))) = do
  (t, s, a) <- infer gamma t
  let vt = eval (env gamma) t
  let primaryMsg = "Refl must only witness equalities of relevant types \
                   \ (irrelevant types are trivially convertible)."
      msg = "Term has type [" ++ ppVal gamma a ++ "] which is irrelevant."
  when (s == Irrelevant) (createError primaryMsg [(pos, msg)])
  pure (Refl t, Irrelevant, eqReduce vt a vt)
infer gamma (R _ (TranspF t@(R pos _) x pf b u t' e)) = do
  (t, s, va) <- infer gamma t
  let msg = "Term has type [" ++ ppVal gamma va ++ "] which is irrelevant."
  when (s == Irrelevant) (createError "Can only transport along relevant types." [(pos, msg)])
  t' <- check gamma t' va
  let vt = eval (env gamma) t
      vt' = eval (env gamma) t'
  let gamma' = bind x Relevant va gamma
      gamma'' = bind pf Irrelevant (eqReduce vt va (head (env gamma'))) gamma'
  b <- check gamma'' b (VU Irrelevant)
  let b_t_refl = eval (VRefl vt : vt : env gamma) b
  u <- check gamma u b_t_refl
  e <- check gamma e (eqReduce vt va vt')
  let ve = eval (env gamma) e
      b_t'_e = eval (ve : vt' : env gamma) b
  pure (Transp t x pf b u t' e, Irrelevant, b_t'_e)
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
  pure (Cast a b e t, s, vb)
infer gamma (R _ (CastReflF a t)) = do
  a <- check gamma a (VU Relevant)
  let va = eval (env gamma) a
  t <- check gamma t va
  let vt = eval (env gamma) t
      cast_a_a_t = cast va va (VRefl vt) vt
      t_eq_cast_a_a_t = eqReduce vt va cast_a_a_t
  pure (CastRefl a t, Irrelevant, t_eq_cast_a_a_t)
infer gamma (R _ (LetF x a t u)) = do
  (a, s) <- checkType gamma a
  let va = eval (env gamma) a
  t <- check gamma t va
  let vt = eval (env gamma) t
  (u, s', uty) <- infer (define x vt s va gamma) u
  pure (Let x a t u, s', uty)
infer gamma (R _ (AnnotationF t a)) = do
  (a, s) <- checkType gamma a
  let va = eval (env gamma) a
  t <- check gamma t va
  pure (Annotation t a, s, va)
infer _ (R pos _) =
  let msg = "Could not infer type for term."
  in createError "Type inference failed." [(pos, msg)]

checkType :: Context -> Raw -> Checker (Term Ix, Relevance)
checkType gamma t@(R pos _) = do
  (t, _, tty) <- infer gamma t
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
check gamma (R _ (PairF t u)) (VExists x a b) = do
  t <- check gamma t a
  let vt = eval (env gamma) t
  u <- check (define x vt Irrelevant a gamma) u (b vt)
  pure (Pair t u)
check gamma (R pos (PairF {})) tty =
  let msg = "Checking pair against type [" ++ ppVal gamma tty ++ "] failed (expected ∃ type)."
  in createError "Pair type checking failed." [(pos, msg)]
check gamma (R _ (LetF x a t u)) uty = do
  (a, s) <- checkType gamma a
  let va = eval (env gamma) a
  t <- check gamma t va
  let vt = eval (env gamma) t
  u <- check (define x vt s va gamma) u uty
  pure (Let x a t u)
check gamma t@(R pos _) tty = do
  (t, _, tty') <- infer gamma t
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
