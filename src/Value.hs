{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Value (
  VElim (..),
  VSpine,
  Val (..),
  pattern VVar,
  pattern VMeta,
  pattern VFun,
  pattern VAnd,
  VTy,
  VProp (..),
  PushArgument (..),
  Closure (..),
  ClosureApply (..),
  appOne,
  A,
  BD (..),
  Env,
  PropEnv,
  level,
  showElimHead,
)
where

import Syntax

import Data.Type.Nat

data BD = Bound | Defined
  deriving (Show)

type Env = [(BD, Val)]

type PropEnv = [(BD, VProp)]

level :: Env -> Lvl
level env = Lvl (length env)

class Applicative f => PushArgument f where
  push :: (a -> f b) -> f (a -> b)

data Closure (n :: Nat) val where
  Closure :: forall n val. [(BD, val)] -> Term Ix -> Closure n val
  Lift :: forall n val. val -> Closure n val
  LiftClosure :: forall n val. Closure n val -> Closure ('S n) val
  Function :: forall n val. (val -> Closure n val) -> Closure ('S n) val

class Applicative f => ClosureApply f (n :: Nat) cl val | val cl -> f where
  app :: ([(BD, val)] -> Term Ix -> f val) -> Closure n val -> cl
  makeFnClosure :: PushArgument f => cl -> f (Closure n val)

instance Applicative f => ClosureApply f 'Z (f val) val where
  app eval (Closure env t) = eval env t
  app _ (Lift v) = pure v

  makeFnClosure v = Lift <$> v

instance ClosureApply f n res val => ClosureApply f ('S n) (val -> res) val where
  app eval (Closure env t) u = app eval (Closure @n (env :> (Bound, u)) t)
  app eval (Lift v) _ = app eval (Lift @n v)
  app eval (LiftClosure cl) _ = app eval cl
  app eval (Function f) u = app eval (f u)

  makeFnClosure f = Function <$> push (makeFnClosure . f)

appOne :: Closure ('S n) val -> val -> Closure n val
appOne (Closure env t) u = Closure (env :> (Bound, u)) t
appOne (Lift v) _ = Lift v
appOne (LiftClosure cl) _ = cl
appOne (Function f) u = f u

type family A n where
  A n = FromGHC n

type VTy = Val

-- Note that [~] is an eliminator for the universe, however it does not
-- have a single point on which it might block. Therefore, it cannot be an
-- eliminator in a spine
data VElim
  = VApp Val
  | VNElim Binder (Closure (A 1) Val) Val Binder Binder (Closure (A 2) Val)
  | VFst
  | VSnd
  | VQElim Binder (Closure (A 1) Val) Binder (Closure (A 1) Val) Binder Binder Binder (Closure (A 3) VProp)
  | VJ VTy Val Binder Binder (Closure (A 2) Val) Val Val
  | VBoxElim
  | VMatch Binder (Closure (A 1) Val) [(Name, Binder, Binder, Closure (A 2) Val)]

showElimHead :: VElim -> String
showElimHead (VApp {}) = "<application>"
showElimHead (VNElim {}) = "<ℕ-elim>"
showElimHead VFst = "<fst>"
showElimHead VSnd = "<snd>"
showElimHead (VQElim {}) = "<Q-elim>"
showElimHead (VJ {}) = "<J>"
showElimHead VBoxElim = "<▢-elim>"
showElimHead (VMatch {}) = "<match>"

type VSpine = [VElim]

data Val
  = VRigid Lvl VSpine
  | VFlex MetaVar Env VSpine
  | VU Relevance
  | VLambda Binder (Closure (A 1) Val)
  | VPi Relevance Binder VTy (Closure (A 1) Val)
  | VZero
  | VSucc Val
  | VNat
  | VExists Binder VTy (Closure (A 1) Val)
  | VAbort VTy VProp
  | VEmpty
  | VProp VProp
  | VUnit
  | VEq Val VTy Val
  | VCast VTy VTy VProp Val
  | VPair Val Val
  | VSigma Binder VTy (Closure (A 1) Val)
  | VQuotient
      VTy
      Binder
      Binder
      (Closure (A 2) Val)
      Binder
      (Closure (A 1) VProp)
      Binder
      Binder
      Binder
      (Closure (A 3) VProp)
      Binder
      Binder
      Binder
      Binder
      Binder
      (Closure (A 5) VProp)
  | VQProj Val
  | VIdRefl Val
  | VIdPath VProp
  | VId VTy Val Val
  | VCons Name Val VProp
  | -- A fixed point will not reduce unless applied to a constructor, so it needs a spine
    VFixedPoint VTy Binder Binder Binder Binder (Closure (A 3) Val) (Closure (A 4) Val) (Maybe Val) VSpine
  | VMu Tag Name VTy Binder [(Name, (Relevance, Binder, Closure (A 2) Val, Closure (A 3) Val))] (Maybe Val)
  | VBoxProof VProp
  | VBox Val

pattern VVar :: Lvl -> Val
pattern VVar x = VRigid x []

pattern VMeta :: MetaVar -> Env -> Val
pattern VMeta mv e = VFlex mv e []

pattern VFun :: Relevance -> VTy -> VTy -> VTy
pattern VFun s a b = VPi s Hole a (Lift b)

pattern VAnd :: VTy -> VTy -> VTy
pattern VAnd a b = VExists Hole a (Lift b)

data VProp
  = PVar Lvl
  | PMeta MetaVar PropEnv
  | PU Relevance
  | PLambda Binder (Closure (A 1) VProp)
  | PApp VProp VProp
  | PPi Relevance Binder VProp (Closure (A 1) VProp)
  | PZero
  | PSucc VProp
  | PNElim Binder (Closure (A 1) VProp) VProp Binder Binder (Closure (A 2) VProp) VProp
  | PNat
  | PPropPair VProp VProp
  | PPropFst VProp
  | PPropSnd VProp
  | PExists Binder VProp (Closure (A 1) VProp)
  | PAbort VProp VProp
  | PEmpty
  | POne
  | PUnit
  | PEq VProp VProp VProp
  | PRefl VProp
  | PSym VProp VProp VProp
  | PTrans VProp VProp VProp VProp VProp
  | PAp VProp Binder (Closure (A 1) VProp) VProp VProp VProp
  | PTransp VProp Binder Binder (Closure (A 2) VProp) VProp VProp VProp
  | PCast VProp VProp VProp VProp
  | PPair VProp VProp
  | PFst VProp
  | PSnd VProp
  | PSigma Binder VProp (Closure (A 1) VProp)
  | PQuotient VProp Binder Binder (Closure (A 2) VProp) Binder (Closure (A 1) VProp) Binder Binder Binder (Closure (A 3) VProp) Binder Binder Binder Binder Binder (Closure (A 5) VProp)
  | PQProj VProp
  | PQElim Binder (Closure (A 1) VProp) Binder (Closure (A 1) VProp) Binder Binder Binder (Closure (A 3) VProp) VProp
  | PIdRefl VProp
  | PIdPath VProp
  | PJ VProp VProp Binder Binder (Closure (A 2) VProp) VProp VProp VProp
  | PId VProp VProp VProp
  | PBoxProof VProp
  | PBoxElim VProp
  | PBox VProp
  | PCons Name VProp VProp
  | PMatch VProp Binder (Closure (A 1) VProp) [(Name, Binder, Binder, Closure (A 2) VProp)]
  | PFixedPoint VProp Binder Binder Binder Binder (Closure (A 3) VProp) (Closure (A 4) VProp)
  | PMu Tag Name VProp Binder [(Name, Relevance, Binder, Closure (A 2) VProp, Closure (A 3) VProp)]
  | PLet Binder VProp VProp (Closure (A 1) VProp)
  | PAnnotation VProp VProp
