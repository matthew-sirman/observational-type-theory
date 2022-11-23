module TypeChecker where

import Control.Monad.Except
import Syntax

type Checker a = Except String a

type Types = [(Name, Relevance, VTy Ix)]

data Context = Context
  { env :: Env Ix,
    types :: Types,
    lvl :: Int
  }

eval :: Env Ix -> Term Ix -> Val Ix
eval env (Var (Ix x)) = env !! x
eval _ (U s) = VU s
eval env (Lambda x _ e) = VLambda x (Closure e env)
eval env (App t u) = eval env t $$ eval env u
eval env (Pi _ x a b) = VPi x (eval env a) (Closure b env)
eval _ Zero = VZero
eval env (Succ n) = VSucc (eval env n)
eval env (NElim a t0 ts n) = recurse (eval env n)
  where
    va, vt0, vts :: Val Ix
    va = eval env a
    vt0 = eval env t0
    vts = eval env ts

    recurse :: Val Ix -> Val Ix
    recurse VZero = vt0
    recurse (VSucc n) = vts $$ n $$ recurse n
    recurse ne = VNElim va vt0 vts ne
eval _ Nat = VNat
eval _ (Pair t u) = VPair t u
eval _ (Fst t) = VFst t
eval _ (Snd t) = VSnd t
eval env (Exists x a b) = VExists x (eval env a) (Closure b env)
eval _ (Abort _ t) = VAbort t
eval _ Empty = VEmpty
eval _ One = VOne
eval _ Unit = VUnit
eval env (Eq t a u) = eqReduce (eval env t) (eval env a) (eval env u)
  where
    eqReduce :: Val Ix -> VTy Ix -> Val Ix -> Val Ix
    -- TODO: probably need to quote [b]
    eqReduce f (VPi x a b) g = VPi x a (Closure (Eq (App t (Var 0)) b (App u (Var 0))) env)
-- Rule Eq-Ω
eval _ (Refl _) = error "BUG: Cannot reduce refl (proof-irrelevant)"
eval _ (Transp {}) = error "BUG: Cannot reduce transport (proof-irrelevant)"
eval env (Cast a b _ t) = VCast (eval env a) (eval env b) (eval env t)
eval _ (CastRefl {}) = error "BUG: Cannot reduce castrefl (proof-irrelevant)"

infixl 8 $$

($$) :: Val Ix -> Val Ix -> Val Ix
(VLambda _ (Closure e env)) $$ u = eval (u : env) e
t $$ u = VApp t u
