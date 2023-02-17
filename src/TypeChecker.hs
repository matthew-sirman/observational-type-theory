{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
-- {-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module TypeChecker where

import Control.Lens hiding (Context, Empty, Refl, (:>))
import Control.Monad.Except
import Control.Monad.Oops (throw)
import Control.Monad.Reader
import Control.Monad.State

import Data.Fix (Fix (..))
import Data.IntMap qualified as IM
import Data.Variant hiding (throw)
import Error.Diagnose

import Error
import Syntax

type Checker e a = ExceptT e (State MetaContext) a

type Types = [(Binder, (Relevance, VTy Ix))]

data Context = Context
  { env :: Env Ix
  , types :: Types
  , lvl :: Lvl
  }

names :: Context -> [Binder]
names = map fst . types

emptyContext :: Context
emptyContext = Context {env = [], types = [], lvl = 0}

data MetaEntry
  = Unsolved [Binder]
  | Solved [Binder] (Val Ix)

data MetaContext = MetaContext
  { _metas :: IM.IntMap MetaEntry
  , _fresh :: MetaVar
  }

makeLenses ''MetaContext

instance Show MetaContext where
  show mctx = "{ " ++ showEntries (IM.assocs (mctx ^. metas)) ++ " }"
    where
      showEntry :: (Int, MetaEntry) -> String
      showEntry (m, Unsolved _) = "?" ++ show m
      showEntry (m, Solved ns v) = "?" ++ show m ++ " := " ++ prettyPrintTerm ns (quote (Lvl (length ns)) v)

      showEntries :: [(Int, MetaEntry)] -> String
      showEntries [] = ""
      showEntries [e] = showEntry e
      showEntries (es :> e) = showEntries es ++ "\n, " ++ showEntry e

emptyMetaContext :: MetaContext
emptyMetaContext = MetaContext {_metas = IM.empty, _fresh = 0}

freshMeta :: [Binder] -> Checker (Variant e) MetaVar
freshMeta ns = do
  mv@(MetaVar v) <- gets (^. fresh)
  fresh += 1
  modify (metas %~ IM.insert v (Unsolved ns))
  pure mv

addSolution :: MetaVar -> Val Ix -> Checker (Variant e) ()
addSolution (MetaVar v) solution = do
  entry <- gets (IM.lookup v . (^. metas))
  case entry of
    Nothing -> error "BUG: IMPOSSIBLE!"
    -- We only solve metas with definitionally unique solutions, so if we
    -- re-solve the meta, we must have something equivalent to what we already
    -- had, so we do nothing (ideally this will never even happen)
    Just (Solved {}) -> pure ()
    Just (Unsolved ns) -> modify (metas %~ IM.insert v (Solved ns solution))

data EvalEnv = EvalEnv
  { evalEnv :: Env Ix
  , evalLvl :: Lvl
  , mctx :: MetaContext
  }

extend :: Val Ix -> EvalEnv -> EvalEnv
extend v env =
  env
    { evalEnv = evalEnv env :> (Bound, v)
    , evalLvl = evalLvl env + 1
    }

extendDef :: Val Ix -> EvalEnv -> EvalEnv
extendDef v env =
  env
    { evalEnv = evalEnv env :> (Defined, v)
    , evalLvl = evalLvl env + 1
    }

bindM2 :: Monad m => (a -> b -> m r) -> m a -> m b -> m r
bindM2 f a b = join (liftM2 f a b)

bindM3 :: Monad m => (a -> b -> c -> m r) -> m a -> m b -> m c -> m r
bindM3 f a b c = join (liftM3 f a b c)

bindM4 :: Monad m => (a -> b -> c -> d -> m r) -> m a -> m b -> m c -> m d -> m r
bindM4 f a b c d = join (liftM4 f a b c d)

-- TODO: need to think properly about interface of evaluation

eqReduce :: EvalEnv -> Val Ix -> VTy Ix -> Val Ix -> Val Ix
eqReduce env vt va vu = eqReduceType va
  where
    -- Initially driven just by the type
    eqReduceType :: VTy Ix -> Val Ix
    -- Rule Eq-Fun
    eqReduceType (VPi s x a b) =
      -- Γ ⊢ f ~[Π(x : A). B] g => Π(x : A). f x ~[B] g x
      -- Γ, x : A ⊢ f x ~[B] g x
      let fx_eq_gx vx = Lift (eqReduce (env & extend vx) (vt $$ VApp vx) (app' (mctx env) b vx) (vu $$ VApp vx))
       in VPi s x a (Function fx_eq_gx)
    -- Rule Eq-Ω
    eqReduceType (VU Irrelevant) =
      let t_to_u = VFun Irrelevant vt vu
          u_to_t = VFun Irrelevant vu vt
       in VAnd t_to_u u_to_t
    -- Rule Id-Proof-Eq
    eqReduceType (VId {}) = VUnit
    -- Other cases require matching on [t] and [u]
    eqReduceType va = eqReduceAll vt va vu

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
          let a_eq_a' = eqReduce env a (VU Relevant) a'
              b_eq_b' ve va' =
                let env'' = env & extend ve & extend va'
                    e = quoteToProp env'' ve
                    va = cast a' a (Sym $$$ e) va'
                 in Lift (eqReduce env'' (app' (mctx env) b va) (VU Relevant) (app' (mctx env) b' va'))
              forall_x'_b_eq_b' ve = Lift (VPi s x' a' (Function (b_eq_b' ve)))
           in VExists (Name "$e") a_eq_a' (Function forall_x'_b_eq_b')
    -- Rule Eq-Σ
    eqReduceAll (VSigma _ a b) (VU Relevant) (VSigma x' a' b') =
      let a_eq_a' = eqReduce env a (VU Relevant) a'
          b_eq_b' ve va' =
            let env'' = env & extend ve & extend va'
                e = quoteToProp env'' ve
                va = cast a' a (Sym $$$ e) va'
             in Lift (eqReduce env'' (app' b va) (VU Relevant) (app' b' va'))
          forall_x'_b_eq_b' ve = Lift (VPi Relevant x' a' (Function (b_eq_b' ve)))
       in VExists (Name "$e") a_eq_a' (Function forall_x'_b_eq_b')
    -- Rule Eq-Quotient
    eqReduceAll (VQuotient a x y r _ _ _ _ _ _ _ _ _ _ _ _) (VU Relevant) (VQuotient a' _ _ r' _ _ _ _ _ _ _ _ _ _ _ _) =
      let a_eq_a' = eqReduce env a (VU Relevant) a'
          rxy_eq_rx'y' ve vx vy =
            let env''' = env & extend ve & extend vx & extend vy
                e = quoteToProp env''' ve
                vx' = cast a a' e vx
                vy' = cast a a' e vy
             in Lift
                  ( eqReduce
                      env'''
                      (app' r vx vy)
                      (VU Irrelevant)
                      (app' r' vx' vy')
                  )
          forall_y_rxy_eq_rx'y' ve vx = Lift (VPi Relevant y a (Function (rxy_eq_rx'y' ve vx)))
          forall_x_y_rxy_eq_rx'y' ve = Lift (VPi Relevant x a (Function (forall_y_rxy_eq_rx'y' ve)))
       in VExists (Name "$e") a_eq_a' (Function forall_x_y_rxy_eq_rx'y')
    -- Rule Eq-Zero
    eqReduceAll VZero VNat VZero = VUnit
    -- Rule Eq-Zero-Succ
    eqReduceAll VZero VNat (VSucc _) = VEmpty
    -- Rule Eq-Succ-Zero
    eqReduceAll (VSucc _) VNat VZero = VEmpty
    -- Rule Eq-Succ
    eqReduceAll (VSucc m) VNat (VSucc n) = eqReduceAll m VNat n
    -- Rule Eq-Pair
    eqReduceAll (VPair t u) (VSigma x a b) (VPair t' u') =
      let t_eq_t' = eqReduce env t a t'
          u_eq_u' ve =
            let env' = env & extend ve
                e = quoteToProp env' ve
                tm_b = quote (evalLvl env + 1) (app' b (VVar (evalLvl env)))
                cast_b_t_b_t' = cast (app' b t) (app' b t') (Ap (Lambda x tm_b) $$$ e)
             in Lift (eqReduce env' (cast_b_t_b_t' u) (app' b t') u')
       in VExists (Name "$e") t_eq_t' (Function u_eq_u')
    -- Rule Quotient-Proj-Eq
    eqReduceAll (VQProj t) (VQuotient _ _ _ r _ _ _ _ _ _ _ _ _ _ _ _) (VQProj u) = app' r t u
    -- Rule Id-Eq
    eqReduceAll (VId a t u) (VU Relevant) (VId a' t' u') =
      let a_eq_a' = eqReduce env a (VU Relevant) a'
          t_eq_t' ve =
            let env' = env & extend ve
                e = quoteToProp env' ve
             in eqReduce env' (cast a a' e t) a' t'
          u_eq_u' ve =
            let env'' = env & extend ve & extend (VVar (evalLvl env + 1))
                e = quoteToProp env'' ve
             in eqReduce env'' (cast a a' e u) a' u'
          t_eq_t'_and_u_eq_u' ve = Lift (VAnd (t_eq_t' ve) (u_eq_u' ve))
       in VExists (Name "$e") a_eq_a' (Function t_eq_t'_and_u_eq_u')
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

cast :: VTy Ix -> VTy Ix -> VProp Ix -> Val Ix -> Val Ix
-- Rule Cast-Zero
cast VNat VNat _ VZero = VZero
-- Rule Cast-Succ
cast VNat VNat e (VSucc n) = VSucc (cast VNat VNat e n)
-- Rule Cast-Univ
cast (VU s) (VU s') _ a
  | s == s' = a
-- Rule Cast-Pi
cast (VPi _ _ a b) (VPi _ x' a' b') e f =
  let cast_b_b' va' =
        let va = cast a' a (Sym . PropFst $$$ e) va'
         in Lift (cast (app' b va) (app' b' va') (PropSnd $$$ e) (f $$ VApp va))
   in VLambda x' (Function cast_b_b')
cast (VSigma _ a b) (VSigma _ a' b') e (VPair t u) =
  let t' = cast a a' (PropFst $$$ e) t
      u' = cast (app' b t) (app' b' t') (PropSnd $$$ e) u
   in VPair t' u'
cast a@(VSigma {}) b@(VSigma {}) e p = cast a b e (VPair (p $$ VFst) (p $$ VSnd))
cast (VQuotient a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (VQuotient a' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) e (VQProj t) =
  VQProj (cast a a' (PropFst $$$ e) t)
cast (VId {}) (VId {}) e (VIdRefl _) =
  VIdPath ((\e -> Trans (Sym (Fst (Snd e))) (Snd (Snd e))) $$$ e)
-- TODO: This is currently horrible, possibly try to come up with a better system for
-- proof manipulation
cast (VId _ _ _) (VId _ _ _) (VProp _ _) (VIdPath (VProp _ _)) = undefined
-- cast (VId va _ _) (VId va' _ _) (VProp pEnv e') (VIdPath (VProp _ e)) =
-- let a = quote lvl va
--     a' = quote lvl va'
-- let t'_eq_t = Sym (Fst (Snd e'))
--     t_eq_u = Ap (Lambda (Name "-") (Cast a a' (Fst e') (Var 0))) e
--     u_eq_u' = Snd (Snd e')
--     t'_eq_u' = Trans t'_eq_t (Trans t_eq_u u_eq_u')
-- pure (VIdPath (VProp env t'_eq_u'))
cast a b e t = VCast a b e t

quoteToProp :: EvalEnv -> Val Ix -> VProp Ix
quoteToProp env = evalProp env . quote (evalLvl env)

evalProp :: EvalEnv -> Term Ix -> VProp Ix
evalProp env = VProp (evalEnv env)

closure :: EvalEnv -> Term Ix -> Closure n Ix
closure env = Closure (evalEnv env)

eval :: EvalEnv -> Term Ix -> Val Ix
eval env (Var (Ix x)) = snd (evalEnv env !! x)
eval _ (U s) = VU s
eval env (Lambda x e) = VLambda x (closure env e)
eval env (App t u) = eval env t $$ VApp (eval env u)
eval env (Pi s x a b) = VPi s x <$> eval a <*> closure b
eval env Zero = pure VZero
eval env (Succ n) = VSucc <$> eval n
eval env (NElim z a t0 x ih ts n) = do
  n <- eval n
  env <- asks evalEnv
  let va = Closure env a
  vt0 <- eval t0
  let vts = Closure env ts
      elim = VNElim z va vt0 x ih vts
  n $$ elim
eval _ Nat = pure VNat
eval env p@(PropPair {}) = VOne <$> evalProp p
eval env p@(PropFst _) = VOne <$> evalProp p
eval env p@(PropSnd _) = VOne <$> evalProp p
eval env (Exists x a b) = VExists x <$> eval a <*> closure b
eval env (Abort a t) = VAbort <$> eval a <*> evalProp t
eval _ Empty = pure VEmpty
eval env p@One = VOne <$> evalProp p
eval _ Unit = pure VUnit
eval env (Eq t a u) = bindM3 eqReduce (eval t) (eval a) (eval u)
eval env p@(Refl _) = VOne <$> evalProp p
eval env p@(Sym {}) = VOne <$> evalProp p
eval env p@(Trans {}) = VOne <$> evalProp p
eval env p@(Ap {}) = VOne <$> evalProp p
eval env p@(Transp {}) = VOne <$> evalProp p
eval env (Cast a b e t) = bindM4 cast (eval a) (eval b) (evalProp e) (eval t)
eval env p@(CastRefl {}) = VOne <$> evalProp p
eval env (Pair t u) = VPair <$> eval t <*> eval u
eval env (Fst p) = elimM (eval p) (pure VFst)
eval env (Snd p) = elimM (eval p) (pure VSnd)
eval env (Sigma x a b) = VSigma x <$> eval a <*> closure b
eval env (Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) = do
  a <- eval a
  r <- closure r
  rr <- evalProp rr
  rs <- evalProp rs
  rt <- evalProp rt
  pure (VQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)
eval env (QProj t) = VQProj <$> eval t
eval env (QElim z b x tpi px py pe p u) = do
  u <- eval u
  b <- closure b
  tpi <- closure tpi
  p <- evalProp p
  u $$ VQElim z b x tpi px py pe p
eval env (IdRefl t) = VIdRefl <$> eval t
eval env (IdPath e) = VIdPath <$> evalProp e
eval env (J a t x pf b u t' e) = do
  a <- eval a
  t <- eval t
  b <- closure b
  u <- eval u
  t' <- eval t'
  e <- eval e
  e $$ VJ a t x pf b u t'
eval env (Id a t u) = VId <$> eval a <*> eval t <*> eval u
eval env (Let _ _ t u) = do
  t <- eval t
  local (extend Defined t) (eval u)
eval env (Annotation t _) = eval t
-- TODO: Return solved metas when present
eval env (Meta mv) = do
  env <- asks evalEnv
  pure (VMeta mv env)

infixl 8 $$

($$) :: Val Ix -> VElim Ix -> Val Ix
(VLambda _ c) $$ (VApp u) = app' c u
VZero $$ (VNElim _ _ t0 _ _ _) = t0
(VSucc n) $$ elim@(VNElim _ _ _ _ _ ts) = app' ts n (n $$ elim)
(VPair t _) $$ VFst = t
(VPair _ u) $$ VSnd = u
(VQProj t) $$ (VQElim _ _ _ tpi _ _ _ _) = app' tpi t
(VIdRefl _) $$ (VJ _ _ _ _ _ u _) = u
-- TODO: Currently a mess (as with other inductive equality)
(VIdPath _) $$ (VJ {}) = undefined
-- (VIdPath _) $$ (VJ _ t _ _ b u t') = do
--   b_t_idrefl_t <- app' b t (VIdRefl t)
--   b_t'_idpath_e <- app' b t' VIdPath
--   env <- asks evalEnv
--   lvl <- asks evalLvl

--   let tm_t = quote lvl t
--       tm_t' = quote lvl t'
--       eqJ = Transp tm_t (Name "x") Hole (quote (lvl + 2) (app'))
--   cast b_t_idrefl_t b_t'_idpath_e (VProp env eqJ) u
-- VOne $$ _ = VOne
(VRigid x sp) $$ u = VRigid x (sp :> u)
(VFlex m env sp) $$ u = VFlex m env (sp :> u)
_ $$ _ = error "BUG: IMPOSSIBLE!"

app' :: ClosureApply n cl Ix => MetaContext -> Closure n Ix -> cl
app' mctx = app eval'
  where
    eval' :: Env Ix -> Term Ix -> Val Ix
    -- TODO: encode length better somehow
    eval' env = eval (EvalEnv {evalEnv = env, evalLvl = Lvl (length env), mctx = mctx})

quoteSp :: Lvl -> Term Ix -> VSpine Ix -> Term Ix
quoteSp _ base [] = base
quoteSp l base (sp :> VApp u) = App (quoteSp l base sp) (quote l u)
quoteSp l base (sp :> VNElim z a t0 x ih ts) =
  NElim z a' (quote l t0) x ih ts' (quoteSp l base sp)
  where
    a', ts' :: Term Ix
    a' = quote (l + 1) (app' a (VVar l))
    ts' = quote (l + 2) (app' ts (VVar l) (VVar (l + 1)))
quoteSp l base (sp :> VFst) = Fst (quoteSp l base sp)
quoteSp l base (sp :> VSnd) = Snd (quoteSp l base sp)
quoteSp l base (sp :> VQElim z b x tpi _ _ _ _) = QElim z b' x tpi' Hole Hole Hole One (quoteSp l base sp)
  where
    b', tpi' :: Term Ix
    b' = quote (l + 1) (app' b (VVar l))
    tpi' = quote (l + 1) (app' tpi (VVar l))
quoteSp l base (sp :> VJ a t x pf b u v) = J a' t' x pf b' u' v' e'
  where
    a', t', b', u', v', e' :: Term Ix
    a' = quote l a
    t' = quote l t
    b' = quote (l + 2) (app' b (VVar l) (VVar (l + 1)))
    u' = quote l u
    v' = quote l v
    e' = quoteSp l base sp

quoteProp' :: Lvl -> Lvl -> VProp Ix -> Term Ix
quoteProp' lvl by (VProp env t) = quoteProp (lvl + by) (VProp (liftEnv by env) t)
  where
    liftEnv :: Lvl -> Env Ix -> Env Ix
    liftEnv 0 env = env
    liftEnv by env = liftEnv (by - 1) env :> (Bound, VVar (lvl + by - 1))

quoteProp :: Lvl -> VProp Ix -> Term Ix
quoteProp lvl (VProp env t) = q env t
  where
    q :: Env Ix -> Term Ix -> Term Ix
    q env (Var (Ix x)) = quote lvl (snd (env !! x))
    q env (Lambda x t) =
      Lambda x (q' 1 env t)
    q env (Pi s x a b) =
      Pi s x (q env a) (q' 1 env b)
    q env (NElim z a t0 x ih ts n) =
      NElim z a' t0' x ih ts' n'
      where
        a', t0', ts' :: Term Ix
        a' = q env a
        t0' = q env t0
        ts' = q' 2 env ts
        n' = q env n
    q env (Exists x a b) =
      Exists x (q env a) (q' 1 env b)
    q env (Transp t x pf b u v e) =
      Transp t' x pf b' u' v' e'
      where
        t', b', u', v', e' :: Term Ix
        t' = q env t
        b' = q' 2 env b
        u' = q env u
        v' = q env v
        e' = q env e
    q env (Sigma x a b) =
      Sigma x (q env a) (q' 1 env b)
    q env (Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) =
      Quotient a' x y r' rx rr' sx sy sxy rs' tx ty tz txy tyz rt'
      where
        a', r', rr', rs', rt' :: Term Ix
        a' = q env a
        r' = q' 2 env r
        rr' = q' 1 env rr
        rs' = q' 3 env rs
        rt' = q' 5 env rt
    q env (QElim z b x tpi px py pe p u) =
      QElim z b' x tpi' px py pe p' u'
      where
        b', tpi', p', u' :: Term Ix
        b' = q' 1 env b
        tpi' = q' 1 env tpi
        p' = q' 3 env p
        u' = q env u
    q env (J a t x pf b u v e) =
      J a' t' x pf b' u' v' e'
      where
        a', t', b', u', v', e' :: Term Ix
        a' = q env a
        t' = q env t
        b' = q' 2 env b
        u' = q env u
        v' = q env v
        e' = q env e
    q env (Let x a t u) =
      Let x (q env a) (q env t) (q' 1 env u)
    q env (Fix t) = Fix (fmap (q env) t)

    q' :: Lvl -> Env Ix -> Term Ix -> Term Ix
    q' by env t = quoteProp' lvl by (VProp env t)

quote :: Lvl -> Val Ix -> Term Ix
quote lvl@(Lvl l) (VRigid (Lvl x) sp) = quoteSp lvl (Var (Ix (l - x - 1))) sp
quote lvl (VFlex mv _ sp) = quoteSp lvl (Meta mv) sp
quote _ (VU s) = U s
quote lvl (VLambda x t) = Lambda x (quote (lvl + 1) (app' t (VVar lvl)))
quote lvl (VPi s x a b) = Pi s x (quote lvl a) (quote (lvl + 1) (app' b (VVar lvl)))
quote _ VZero = Zero
quote lvl (VSucc t) = Succ (quote lvl t)
quote _ VNat = Nat
quote lvl (VExists x a b) =
  Exists x (quote lvl a) (quote (lvl + 1) (app' b (VVar lvl)))
quote lvl (VAbort a t) = Abort (quote lvl a) (quoteProp lvl t)
quote _ VEmpty = Empty
quote lvl (VOne t) = quoteProp lvl t
quote _ VUnit = Unit
quote lvl (VEq t a u) = Eq (quote lvl t) (quote lvl a) (quote lvl u)
quote lvl (VCast a b e t) = Cast (quote lvl a) (quote lvl b) (quoteProp lvl e) (quote lvl t)
quote lvl (VPair t u) = Pair (quote lvl t) (quote lvl u)
quote lvl (VSigma x a b) =
  Sigma x (quote lvl a) (quote (lvl + 1) (app' b (VVar lvl)))
quote lvl (VQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) =
  Quotient
    (quote lvl a)
    x
    y
    (quote (lvl + 2) (app' r (VVar lvl) (VVar (lvl + 1))))
    rx
    (quoteProp' lvl 1 rr)
    sx
    sy
    sxy
    (quoteProp' lvl 3 rs)
    tx
    ty
    tz
    txy
    tyz
    (quoteProp' lvl 5 rt)
quote lvl (VQProj t) = QProj (quote lvl t)
quote lvl (VIdRefl t) = IdRefl (quote lvl t)
quote lvl (VIdPath e) = IdPath (quoteProp lvl e)
quote lvl (VId a t u) = Id (quote lvl a) (quote lvl t) (quote lvl u)

normalForm :: EvalEnv -> Term Ix -> Term Ix
normalForm t = do
  lvl <- asks (Lvl . length . evalEnv)
  quote lvl <$> eval t

bind :: Binder -> Relevance -> VTy Ix -> Context -> Context
bind x s tty ctx =
  ctx
    { types = types ctx :> (x, (s, tty))
    , lvl = lvl ctx + 1
    , env = env ctx :> (Bound, VVar (lvl ctx))
    }

bindR, bindP :: Binder -> VTy Ix -> Context -> Context
bindR x = bind x Relevant
bindP x = bind x Irrelevant

define :: Binder -> Val Ix -> Relevance -> VTy Ix -> Context -> Context
define x t s tty ctx =
  ctx
    { types = types ctx :> (x, (s, tty))
    , lvl = lvl ctx + 1
    , env = env ctx :> (Defined, t)
    }

data PartialRenaming = PRen
  { renaming :: IM.IntMap Lvl
  , dom :: Lvl
  , cod :: Lvl
  }

-- Γ -> Γ ⊢ σ : Δ -> Δ ⊢ σ' : Γ
invert
  :: forall e
   . e `CouldBe` UnificationError
  => Position
  -> [Binder]
  -> Lvl
  -> Env Ix
  -> Checker (Variant e) PartialRenaming
invert pos names gamma sub = do
  (dom, renaming) <- inv sub
  pure (PRen {renaming = renaming, dom = dom, cod = gamma})
  where
    inv :: Env Ix -> Checker (Variant e) (Lvl, IM.IntMap Lvl)
    inv [] = pure (0, IM.empty)
    inv (sub :> (Defined, _)) = do
      (dom, renaming) <- inv sub
      pure (dom + 1, renaming)
    inv (sub :> (Bound, VVar (Lvl x))) = do
      (dom, renaming) <- inv sub
      when (IM.member x renaming) (throw (NonLinearSpineDuplicate (show (names !! x)) pos))
      pure (dom + 1, IM.insert x dom renaming)
    inv (_ :> (Bound, t)) =
      throw (NonLinearSpineNonVariable (TS (prettyPrintTerm names (quote gamma t))) pos)

renameEnv
  :: forall e
   . e `CouldBe` UnificationError
  => Position
  -> [Binder]
  -> MetaVar
  -> PartialRenaming
  -> Env Ix
  -> Checker (Variant e) (Env Ix)
renameEnv _ _ _ _ [] = pure []
renameEnv pos ns m sub (env :> (bd, v)) = do
  env <- renameEnv pos ns m sub env
  v <- rename pos ns m sub v
  pure (env :> (bd, v))

renameClosure
  :: forall e a
   . e `CouldBe` UnificationError
  => Position
  -> [Binder]
  -> MetaVar
  -> PartialRenaming
  -> Closure a Ix
  -> Checker (Variant e) (Closure a Ix)
renameClosure pos ns m sub (Closure env t) =
  Closure <$> renameEnv pos ns m sub env <*> pure t
renameClosure pos ns m sub (Lift v) = Lift <$> rename pos ns m sub v

renameProp
  :: forall e
   . e `CouldBe` UnificationError
  => Position
  -> [Binder]
  -> MetaVar
  -> PartialRenaming
  -> VProp Ix
  -> Checker (Variant e) (VProp Ix)
renameProp pos ns m sub (VProp env t) = VProp <$> renameEnv pos ns m sub env <*> pure t

renameSp
  :: forall e
   . e `CouldBe` UnificationError
  => Position
  -> [Binder]
  -> MetaVar
  -> PartialRenaming
  -> VSpine Ix
  -> Checker (Variant e) (VSpine Ix)
renameSp _ _ _ _ [] = pure []
renameSp pos ns m sub (sp :> VApp u) = do
  sp <- renameSp pos ns m sub sp
  u <- rename pos ns m sub u
  pure (sp :> VApp u)
renameSp pos ns m sub (sp :> VNElim z a t0 x ih ts) = do
  sp <- renameSp pos ns m sub sp
  a <- renameClosure pos ns m sub a
  t0 <- rename pos ns m sub t0
  ts <- renameClosure pos ns m sub ts
  pure (sp :> VNElim z a t0 x ih ts)
renameSp pos ns m sub (sp :> VFst) = do
  sp <- renameSp pos ns m sub sp
  pure (sp :> VFst)
renameSp pos ns m sub (sp :> VSnd) = do
  sp <- renameSp pos ns m sub sp
  pure (sp :> VSnd)
renameSp pos ns m sub (sp :> VQElim z b x tpi px py pe p) = do
  sp <- renameSp pos ns m sub sp
  b <- renameClosure pos ns m sub b
  tpi <- renameClosure pos ns m sub tpi
  p <- renameProp pos ns m sub p
  pure (sp :> VQElim z b x tpi px py pe p)
renameSp pos ns m sub (sp :> VJ a t x pf b u v) = do
  sp <- renameSp pos ns m sub sp
  a <- rename pos ns m sub a
  t <- rename pos ns m sub t
  b <- renameClosure pos ns m sub b
  u <- rename pos ns m sub u
  v <- rename pos ns m sub v
  pure (sp :> VJ a t x pf b u v)

rename
  :: forall e
   . e `CouldBe` UnificationError
  => Position
  -> [Binder]
  -> MetaVar
  -> PartialRenaming
  -> Val Ix
  -> Checker (Variant e) (Val Ix)
rename pos ns m sub (VRigid (Lvl x) sp) =
  case IM.lookup x (renaming sub) of
    Nothing -> throw (EscapingVariable (show (ns !! x)) pos)
    Just x' -> VRigid x' <$> renameSp pos ns m sub sp
rename pos ns m sub (VFlex m' env sp)
  -- TODO: Need to in fact check DAG ordering, not just single MetaVar occurrence.
  -- e.g. might have α := λx. β, β := α (neither directly violate occurs check, but clearly
  -- unsolvable)
  | m == m' = throw (OccursCheck m pos)
  | otherwise = do
      env <- renameEnv pos ns m sub env
      sp <- renameSp pos ns m sub sp
      pure (VFlex m' env sp)
rename _ _ _ _ (VU s) = pure (VU s)
rename pos ns m sub (VLambda x t) = VLambda x <$> renameClosure pos ns m sub t
rename pos ns m sub (VPi s x a b) = do
  a <- rename pos ns m sub a
  b <- renameClosure pos ns m sub b
  pure (VPi s x a b)
rename _ _ _ _ VZero = pure VZero
rename pos ns m sub (VSucc n) = VSucc <$> rename pos ns m sub n
rename _ _ _ _ VNat = pure VNat
rename pos ns m sub (VExists x a b) = do
  a <- rename pos ns m sub a
  b <- renameClosure pos ns m sub b
  pure (VExists x a b)
rename pos ns m sub (VAbort a t) = do
  a <- rename pos ns m sub a
  t <- renameProp pos ns m sub t
  pure (VAbort a t)
rename _ _ _ _ VEmpty = pure VEmpty
rename pos ns m sub (VOne p) = VOne <$> renameProp pos ns m sub p
rename _ _ _ _ VUnit = pure VUnit
rename pos ns m sub (VEq t a u) = do
  t <- rename pos ns m sub t
  a <- rename pos ns m sub a
  u <- rename pos ns m sub u
  -- As the substitution strictly replaces variables with variables,
  -- a blocked [~] will still be blocked, therefore we don't need to
  -- reduce it.
  pure (VEq t a u)
rename pos ns m sub (VCast a b e t) = do
  a <- rename pos ns m sub a
  b <- rename pos ns m sub b
  e <- renameProp pos ns m sub e
  t <- rename pos ns m sub t
  -- As with [~], [cast] must have been blocked, and therefore must still
  -- be blocked.
  pure (VCast a b e t)
rename pos ns m sub (VPair t u) = do
  t <- rename pos ns m sub t
  u <- rename pos ns m sub u
  pure (VPair t u)
rename pos ns m sub (VSigma x a b) = do
  a <- rename pos ns m sub a
  b <- renameClosure pos ns m sub b
  pure (VSigma x a b)
rename pos ns m sub (VQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) = do
  a <- rename pos ns m sub a
  r <- renameClosure pos ns m sub r
  rr <- renameProp pos ns m sub rr
  rs <- renameProp pos ns m sub rs
  rt <- renameProp pos ns m sub rt
  pure (VQuotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)
rename pos ns m sub (VQProj t) = VQProj <$> rename pos ns m sub t
rename pos ns m sub (VIdRefl t) = VIdRefl <$> rename pos ns m sub t
rename pos ns m sub (VIdPath e) = VIdPath <$> renameProp pos ns m sub e
rename pos ns m sub (VId a t u) = do
  a <- rename pos ns m sub a
  t <- rename pos ns m sub t
  u <- rename pos ns m sub u
  pure (VId a t u)

-- Solve a metavariable, possibly applied to a spine of eliminators
solve
  :: e `CouldBe` UnificationError
  => Position
  -> [Binder]
  -> Lvl
  -> MetaVar
  -> Env Ix
  -> VSpine Ix
  -> Val Ix
  -> Checker (Variant e) ()
solve pos names lvl mv sub [] t = do
  inv <- invert pos names lvl sub
  t' <- rename pos names mv inv t
  addSolution mv t'
solve pos names lvl mv sub (sp :> VApp u@(VVar (Lvl x))) t = do
  body <- freshMeta names
  solve pos names (lvl + 1) body (sub :> (Bound, u)) sp t
  addSolution mv (VLambda (names !! x) (Closure sub (Meta body)))
solve pos names lvl _ _ (_ :> VApp u) _ =
  throw (NonLinearSpineNonVariable (TS (prettyPrintTerm names (quote lvl u))) pos)
solve _ _ _ _ _ _ _ = error "Not yet implemented!"

conv
  :: forall e
   . ( e `CouldBe` ConversionError
     , e `CouldBe` UnificationError
     )
  => Position
  -> [Binder]
  -> Lvl
  -> Val Ix
  -> Val Ix
  -> Checker (Variant e) ()
conv pos names = conv' names names
  where
    convSp
      :: [Binder]
      -> [Binder]
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
      conv' (ns :> z) (ns' :> z') (lvl + 1) (app' a (VVar lvl)) (app' a' (VVar lvl))
      conv' ns ns' lvl t0 t0'
      conv'
        (ns :> x :> ih)
        (ns' :> x' :> ih')
        (lvl + 2)
        (app' ts (VVar lvl) (VVar (lvl + 1)))
        (app' ts' (VVar lvl) (VVar (lvl + 1)))
    convSp ns ns' lvl (sp :> VFst) (sp' :> VFst) = convSp ns ns' lvl sp sp'
    convSp ns ns' lvl (sp :> VSnd) (sp' :> VSnd) = convSp ns ns' lvl sp sp'
    convSp ns ns' lvl (sp :> VQElim z b x tpi _ _ _ _) (sp' :> VQElim z' b' x' tpi' _ _ _ _) = do
      convSp ns ns' lvl sp sp'
      conv' (ns :> z) (ns' :> z') (lvl + 1) (app' b (VVar lvl)) (app' b' (VVar lvl))
      conv' (ns :> x) (ns' :> x') (lvl + 1) (app' tpi (VVar lvl)) (app' tpi' (VVar lvl))
    convSp ns ns' lvl (sp :> VJ a t x pf b u v) (sp' :> VJ a' t' x' pf' b' u' v') = do
      convSp ns ns' lvl sp sp'
      conv' ns ns' lvl a a'
      conv' ns ns' lvl t t'
      conv'
        (ns :> x :> pf)
        (ns' :> x' :> pf')
        (lvl + 2)
        (app' b (VVar lvl) (VVar (lvl + 1)))
        (app' b' (VVar lvl) (VVar (lvl + 1)))
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
      :: [Binder] -> [Binder] -> Lvl -> Val Ix -> Val Ix -> Checker (Variant e) ()
    -- Rigid-rigid conversion: heads must be equal and spines convertible
    conv' ns ns' lvl (VRigid x sp) (VRigid x' sp')
      | x == x' = convSp ns ns' lvl sp sp'
    -- Flex conversion: attempt to unify
    conv' ns _ lvl (VFlex m env sp) t = solve pos ns lvl m env sp t
    conv' _ ns lvl t (VFlex m env sp) = solve pos ns lvl m env sp t
    conv' _ _ _ (VU s) (VU s')
      | s == s' = pure ()
      | otherwise = throw (ConversionBetweenUniverses pos)
    conv' ns ns' lvl (VLambda x t) (VLambda x' t') =
      conv' (ns :> x) (ns' :> x') (lvl + 1) (app' t (VVar lvl)) (app' t' (VVar lvl))
    conv' ns ns' lvl (VLambda x t) t' =
      conv' (ns :> x) (ns' :> x) (lvl + 1) (app' t (VVar lvl)) (t' $$ VApp (VVar lvl))
    conv' ns ns' lvl t (VLambda x' t') =
      conv' (ns :> x') (ns' :> x') (lvl + 1) (t $$ VApp (VVar lvl)) (app' t' (VVar lvl))
    conv' ns ns' lvl (VPi s x a b) (VPi s' x' a' b')
      | s == s' = do
          conv' ns ns' lvl a a'
          conv' (ns :> x) (ns' :> x') (lvl + 1) (app' b (VVar lvl)) (app' b' (VVar lvl))
    conv' _ _ _ VZero VZero = pure ()
    conv' ns ns' lvl (VSucc n) (VSucc n') = conv' ns ns' lvl n n'
    conv' _ _ _ VNat VNat = pure ()
    conv' ns ns' lvl (VExists x a b) (VExists x' a' b') = do
      conv' ns ns' lvl a a'
      conv' (ns :> x) (ns' :> x') (lvl + 1) (app' b (VVar lvl)) (app' b' (VVar lvl))
    -- Both terms have the same type (by invariant), so [a ≡ a'], and [t] and [t'] are
    -- both of type [⊥], thus also convertible.
    conv' _ _ _ (VAbort {}) (VAbort {}) = pure ()
    conv' _ _ _ VEmpty VEmpty = pure ()
    -- Proof irrelevant, so always convertible
    conv' _ _ _ (VOne {}) _ = pure ()
    conv' _ _ _ _ (VOne {}) = pure ()
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
      conv' (ns :> x) (ns' :> x') (lvl + 1) (app' b (VVar lvl)) (app' b' (VVar lvl))
    conv' ns ns' lvl (VQuotient a x y r _ _ _ _ _ _ _ _ _ _ _ _) (VQuotient a' x' y' r' _ _ _ _ _ _ _ _ _ _ _ _) = do
      conv' ns ns' lvl a a'
      conv'
        (ns :> x :> y)
        (ns' :> x' :> y')
        (lvl + 2)
        (app' r (VVar lvl) (VVar (lvl + 1)))
        (app' r' (VVar lvl) (VVar (lvl + 1)))
    conv' ns ns' lvl (VQProj t) (VQProj t') = conv' ns ns' lvl t t'
    conv' ns ns' lvl (VIdRefl t) (VIdRefl t') = conv' ns ns' lvl t t'
    conv' _ _ _ (VIdPath _) (VIdPath _) = pure ()
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
    find (types :> (Name x, (s, a))) x'
      | x == x' = pure (0, a, s)
      | otherwise = do
          (i, a, s) <- find types x'
          pure (i + 1, a, s)
    find (types :> (Hole, _)) x' = do
      (i, a, s) <- find types x'
      pure (i + 1, a, s)

infer
  :: ( e `CouldBe` InferenceError
     , e `CouldBe` CheckError
     , e `CouldBe` ConversionError
     , e `CouldBe` UnificationError
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
      pure (App t u, app' b vu, s)
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
  let a0 = eval (env gamma :> (Bound, VZero)) a
  t0 <- check gamma t0 a0
  let vx = VVar (lvl gamma)
  let an = eval (env gamma :> (Bound, vx)) a
      aSn = eval (env gamma :> (Bound, VSucc vx)) a
  ts <- check (gamma & bindR x VNat & bind ih s an) ts aSn
  -- In general, argument to inductor should be inferred, but can be checked
  -- in simple case of Nat
  n <- check gamma n VNat
  let vn = eval (env gamma) n
  pure (NElim z a t0 x ih ts n, eval (env gamma :> (Bound, vn)) a, s)
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
    VExists _ _ b -> pure (PropSnd t, app' b VOne, Irrelevant)
    VSigma _ _ b ->
      let vt = eval (env gamma) t
       in pure (Snd t, app' b (vt $$ VFst), Relevant)
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
  let b_t_refl = eval (env gamma :> (Bound, vt) :> (Bound, VOne)) b
  u <- check gamma u b_t_refl
  e <- check gamma e (eqReduce vt va vt')
  let b_t'_e = eval (env gamma :> (Bound, vt') :> (Bound, VOne)) b
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
  let vrxx = eval (env gamma :> (Bound, vx) :> (Bound, vx)) r
  rr <- check (gamma & bindR x va) rr vrxx
  let vrxy = eval (env gamma :> (Bound, vx) :> (Bound, vy)) r
      vryx = eval (env gamma :> (Bound, vy) :> (Bound, vx)) r
  rs <- check (gamma & bindR sx va & bindR sy va & bindP sxy vrxy) rs vryx
  let vryz = eval (env gamma :> (Bound, vy) :> (Bound, vz)) r
      vrxz = eval (env gamma :> (Bound, vx) :> (Bound, vz)) r
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
    VQuotient a _ _ r _ _ _ _ _ _ _ _ _ _ _ _ -> do
      (b, s) <- checkType (gamma & bindR z uty) b
      let vx = VVar (lvl gamma)
          vy = VVar (lvl gamma + 1)
      let b_pix = eval (env gamma :> (Bound, VQProj vx)) b
          b_piy = eval (env gamma :> (Bound, VQProj vy)) b
      tpi <- check (gamma & bindR x a) tpi b_pix
      let tpi_x = eval (env gamma :> (Bound, vx)) tpi
          tpi_y = eval (env gamma :> (Bound, vy)) tpi
          cast_b_piy_b_pix = cast b_piy b_pix tpi_y
          tpi_x_eq_tpi_y = eqReduce tpi_x b_pix cast_b_piy_b_pix
      p <-
        check
          (gamma & bindR px a & bindR py a & bindP pe (app' r vx vy))
          p
          tpi_x_eq_tpi_y
      let vu = eval (env gamma) u
          bu = eval (env gamma :> (Bound, vu)) b
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
  let b_t_idrefl_t = eval (env gamma :> (Bound, vt) :> (Bound, VIdRefl vt)) b
  u <- check gamma u b_t_idrefl_t
  t' <- check gamma t' va
  let vt' = eval (env gamma) t'
  e <- check gamma e (VId va vt vt')
  let ve = eval (env gamma) e
  let b_t'_e = eval (env gamma :> (Bound, vt') :> (Bound, ve)) b
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
infer gamma (R _ HoleF) = do
  a <- freshMeta (names gamma)
  let va = eval (env gamma) (Meta a)
  t <- freshMeta (names gamma)
  -- TODO: Some form of universe metas
  pure (Meta t, va, Relevant)
infer _ (R pos _) = throw (InferenceFailure pos)

checkType
  :: ( e `CouldBe` CheckError
     , e `CouldBe` InferenceError
     , e `CouldBe` ConversionError
     , e `CouldBe` UnificationError
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
     , e `CouldBe` UnificationError
     )
  => Context
  -> Raw
  -> VTy Ix
  -> Checker (Variant e) (Term Ix)
check gamma (R _ (LambdaF x t)) (VPi s _ a b) = do
  let b' = app' b (VVar (lvl gamma))
  t <- check (bind x s a gamma) t b'
  pure (Lambda x t)
check gamma (R pos (LambdaF {})) tty = throw (CheckLambda (ppVal gamma tty) pos)
check gamma (R _ (PropPairF t u)) (VExists _ a b) = do
  t <- check gamma t a
  u <- check gamma u (app' b VOne)
  pure (PropPair t u)
check gamma (R pos (PropPairF {})) tty =
  throw (CheckPropPair (ppVal gamma tty) pos)
check gamma (R _ (PairF t u)) (VSigma _ a b) = do
  t <- check gamma t a
  let vt = eval (env gamma) t
  u <- check gamma u (app' b vt)
  pure (Pair t u)
check gamma (R pos (PairF {})) tty = throw (CheckPair (ppVal gamma tty) pos)
check gamma (R _ (QProjF t)) (VQuotient a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) =
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
