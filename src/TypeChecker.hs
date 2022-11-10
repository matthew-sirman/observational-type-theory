module TypeChecker where

import Control.Monad.Except
import Syntax

type Checker a = Except String a

type Raw = Term Name

type Types = [(Name, Relevance, VTy)]

data Context = Context
  { env :: Env,
    types :: Types,
    lvl :: Int
  }

eval :: Env -> Term Ix -> Val
eval env (Var (Ix x)) = env !! x
eval _ (U s) = VU s
eval env (Lambda x e) = VLambda x (Closure e env)
eval env (App t u) = eval env t $$ eval env u
eval env (Pi s x a b) = VPi s x (eval env a) (Closure b env)
eval _ Zero = VZero
eval env (Succ n) = VSucc (eval env n)
eval env (NElim a t0 ts n) = recurse (eval env n)
  where
    recurse :: Val -> Val
    recurse VZero = eval env t0
    recurse (VSucc n) = eval env ts $$ n $$ recurse n
    recurse ne = VNElim (eval env a) (eval env t0) (eval env ts) ne
eval _ Nat = WNat
eval _ (Pair _ _) = error "BUG: Cannot reduce pairs (proof-irrelevant)"
eval _ (Fst _) = error "BUG: Cannot reduce fst (proof-irrelevant)"
eval _ (Snd _) = error "BUG: Cannot reduce snd (proof-irrelevant)"
eval env (Exists x a b) = VExists x (eval env a) (Closure b env)
eval env (Abort a t) = VAbort (eval env a) (eval env t)
eval _ Empty = VEmpty
eval _ One = error "BUG: Cannot reduce one (proof-irrelevant)"
eval _ Unit = VUnit
eval env (Eq t a u) =
  case eval env a of
    -- Rule Eq-Fun
    -- TODO: ????????????
    VPi s x a b -> VPi s x a (Closure (Eq (App t (Var 0)) b (App g (Var 0))) env)
-- Rule Eq-Ω
eval env (Eq a (U Irrelevant _) b) =
  let va = eval env a
      vb = eval env b
   in VAnd (VFun va vb) (VFun vb va)
-- Rule Eq-Univ
eval _ (Eq Nat (U Relevant _) Nat) = VUnit
eval _ (Eq (U s i) (U Relevant _) (U s' i'))
  | s == s' && i == i' = VUnit
-- Rule Eq-Univ (not equal)
eval env (Eq a (U Relevant _) b)
  | notHdEq (eval env a) (eval env b) = VEmpty
  where
    notHdEq :: VTy -> VTy -> Bool
    notHdEq VNat (VPi {}) = False
    notHdEq VNat (VU {}) = False
    notHdEq (VPi {}) VNat = False
    notHdEq (VPi {}) (VU {}) = False
    notHdEq (VU {}) VNat = False
    notHdEq (VU {}) (VPi {}) = False
    notHdEq (VU s _) (VU s' _) = s == s'
    notHdEq _ _ = True
-- Rule Eq-Π
eval env (Eq (Pi _ _ _ _ a b) (U Relevant k) (Pi _ _ _ _ a' b')) =
  let va = eval env a
      va' = eval env a'
  in
  -- TODO: Fix this rule! This is very wrong
  VExists "e" (VEq va (VU Relevant k) va') (Closure env (Pi _ _ _ "a'" a' (Eq b (U Relevant k) b')))
eval _ (Refl _) = error "BUG: Cannot reduce refl (proof-irrelevant)"
eval _ (Transp {}) = error "BUG: Cannot reduce transport (proof-irrelevant)"
eval env (Cast a b _ t) = VCast (eval env a) (eval env b) (eval env t)
eval _ (CastRefl {}) = error "BUG: Cannot reduce castrefl (proof-irrelevant)"

infixl 8 $$

($$) :: Val -> Val -> Val
(VLambda _ (Closure e env)) $$ u = eval (u : env) e
t $$ u = VApp t u

conv :: Int -> Val -> Val -> Checker ()
conv = undefined

check :: Context -> Raw -> VTy -> Checker (Term Ix)
check gamma (Pair u t) (VExists _ a b) = do
  u <- check gamma u a
  let vu = eval (env gamma) u
  t <- check gamma t (b $$ vu)
  pure (Pair u t)

infer :: Context -> Raw -> Checker (Term Ix, VTy)
infer = undefined
