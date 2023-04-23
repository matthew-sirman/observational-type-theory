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
  VFunctorInstance (..),
  pattern VVar,
  pattern VMeta,
  pattern VFun,
  pattern VAnd,
  ValProp (..),
  embedProp,
  VTy,
  VProp (..),
  PFunctorInstance (..),
  PushArgument (..),
  Closure (..),
  PropClosure,
  ValClosure,
  ClosureApply (..),
  appOne,
  A,
  BD (..),
  Env,
  level,
  extend,
  var,
  showElimHead,
)
where

import Syntax

import Data.Type.Nat

data BD = Bound | Defined
  deriving (Show)

type Env v = [(BD, v)]

level :: Env v -> Lvl
level env = Lvl (length env)

extend :: Lvl -> Env ValProp -> Env ValProp
extend lvl env = env :> (Bound, var lvl)

class Applicative f => PushArgument f where
  push :: (a -> f b) -> f (a -> b)

data Closure (n :: Nat) val cod where
  Closure :: forall n val cod. Env val -> Term Ix -> Closure n val cod
  Lift :: forall n val cod. cod -> Closure n val cod
  LiftClosure :: forall n val cod. Closure n val cod -> Closure ('S n) val cod
  Function :: forall n val cod. (val -> Closure n val cod) -> Closure ('S n) val cod

class Applicative f => ClosureApply f (n :: Nat) cl val cod | val cod cl -> f where
  app :: ([(BD, val)] -> Term Ix -> f cod) -> Closure n val cod -> cl
  makeFnClosure :: PushArgument f => cl -> f (Closure n val cod)

instance Applicative f => ClosureApply f 'Z (f cod) val cod where
  app eval (Closure env t) = eval env t
  app _ (Lift v) = pure v

  makeFnClosure v = Lift <$> v

instance ClosureApply f n res val cod => ClosureApply f ('S n) (val -> res) val cod where
  app eval (Closure env t) u = app eval (Closure @n (env :> (Bound, u)) t)
  app eval (Lift v) _ = app eval (Lift @n v)
  app eval (LiftClosure cl) _ = app eval cl
  app eval (Function f) u = app eval (f u)

  makeFnClosure f = Function <$> push (makeFnClosure . f)

appOne :: Closure ('S n) val cod -> val -> Closure n val cod
appOne (Closure env t) u = Closure (env :> (Bound, u)) t
appOne (Lift v) _ = Lift v
appOne (LiftClosure cl) _ = cl
appOne (Function f) u = f u

type family A n where
  A n = FromGHC n

data ValProp = ValProp
  { val :: Val
  , prop :: VProp
  }

embedProp :: VProp -> ValProp
embedProp p = ValProp {val = VProp p, prop = p}

var :: Lvl -> ValProp
var lvl = ValProp {val = VVar lvl, prop = PVar lvl}

type VTy = Val

type ValClosure n = Closure n ValProp Val

type PropClosure n = Closure n VProp VProp

-- Note that [~] is an eliminator for the universe, however it does not
-- have a single point on which it might block. Therefore, it cannot be an
-- eliminator in a spine
data VElim
  = VApp Val
  | VNElim Binder (ValClosure (A 1)) Val Binder Binder (ValClosure (A 2))
  | VFst
  | VSnd
  | VQElim Binder (ValClosure (A 1)) Binder (ValClosure (A 1)) Binder Binder Binder (PropClosure (A 3))
  | VJ VTy Val Binder Binder (ValClosure (A 2)) Val Val
  | VBoxElim
  | VMatch Binder (ValClosure (A 1)) [(Name, Binder, Binder, ValClosure (A 2))]

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
  = VNeutral Val VSpine
  | VRigid Lvl
  | VFlex MetaVar (Env ValProp)
  | VU Relevance
  | VLambda Binder (ValClosure (A 1))
  | VPi Relevance Binder VTy (ValClosure (A 1))
  | VZero
  | VSucc Val
  | VNat
  | VExists Binder VTy (ValClosure (A 1))
  | VAbort VTy VProp
  | VEmpty
  | VProp VProp
  | VUnit
  | VEq Val VTy Val
  | VCast VTy VTy VProp Val
  | VPair Val Val
  | VSigma Binder VTy (ValClosure (A 1))
  | VQuotient
      VTy
      Binder
      Binder
      (ValClosure (A 2))
      Binder
      (PropClosure (A 1))
      Binder
      Binder
      Binder
      (PropClosure (A 3))
      Binder
      Binder
      Binder
      Binder
      Binder
      (PropClosure (A 5))
  | VQProj Val
  | VIdRefl Val
  | VIdPath VProp
  | VId VTy Val Val
  | VCons Name Val VProp
  | VFixedPoint VTy Binder Binder Binder Binder Binder (ValClosure (A 4)) (ValClosure (A 5)) (Maybe Val)
  | VMu Tag Name VTy Binder [(Name, (Relevance, Binder, ValClosure (A 2), ValClosure (A 3)))] (Maybe VFunctorInstance) (Maybe Val)
  | VBoxProof VProp
  | VBox Val

data VFunctorInstance = VFunctorInstance Binder Binder Binder Binder Binder (ValClosure (A 5))

pattern VVar :: Lvl -> Val
pattern VVar lvl = VNeutral (VRigid lvl) []

pattern VMeta :: MetaVar -> Env ValProp -> Val
pattern VMeta mv env = VNeutral (VFlex mv env) []

pattern VFun :: Relevance -> VTy -> VTy -> VTy
pattern VFun s a b = VPi s Hole a (Lift b)

pattern VAnd :: VTy -> VTy -> VTy
pattern VAnd a b = VExists Hole a (Lift b)

data VProp
  = PVar Lvl
  | PMeta MetaVar (Env VProp)
  | PU Relevance
  | PLambda Binder (PropClosure (A 1))
  | PApp VProp VProp
  | PPi Relevance Binder VProp (PropClosure (A 1))
  | PZero
  | PSucc VProp
  | PNElim Binder (PropClosure (A 1)) VProp Binder Binder (PropClosure (A 2)) VProp
  | PNat
  | PPropPair VProp VProp
  | PPropFst VProp
  | PPropSnd VProp
  | PExists Binder VProp (PropClosure (A 1))
  | PAbort VProp VProp
  | PEmpty
  | POne
  | PUnit
  | PEq VProp VProp VProp
  | PRefl VProp
  | PSym VProp VProp VProp
  | PTrans VProp VProp VProp VProp VProp
  | PAp VProp Binder (PropClosure (A 1)) VProp VProp VProp
  | PTransp VProp Binder Binder (PropClosure (A 2)) VProp VProp VProp
  | PCast VProp VProp VProp VProp
  | PPair VProp VProp
  | PFst VProp
  | PSnd VProp
  | PSigma Binder VProp (PropClosure (A 1))
  | PQuotient VProp Binder Binder (PropClosure (A 2)) Binder (PropClosure (A 1)) Binder Binder Binder (PropClosure (A 3)) Binder Binder Binder Binder Binder (PropClosure (A 5))
  | PQProj VProp
  | PQElim Binder (PropClosure (A 1)) Binder (PropClosure (A 1)) Binder Binder Binder (PropClosure (A 3)) VProp
  | PIdRefl VProp
  | PIdPath VProp
  | PJ VProp VProp Binder Binder (PropClosure (A 2)) VProp VProp VProp
  | PId VProp VProp VProp
  | PBoxProof VProp
  | PBoxElim VProp
  | PBox VProp
  | PCons Name VProp VProp
  | PIn VProp
  | POut VProp
  | PFLift VProp VProp
  | PFmap VProp VProp VProp VProp VProp VProp
  | PMatch VProp Binder (PropClosure (A 1)) [(Name, Binder, Binder, PropClosure (A 2))]
  | PFixedPoint VProp Binder Binder Binder Binder Binder (PropClosure (A 4)) (PropClosure (A 5))
  | PMu Tag Name VProp Binder [(Name, Relevance, Binder, PropClosure (A 2), PropClosure (A 3))] (Maybe PFunctorInstance)
  | PLet Binder VProp VProp (PropClosure (A 1))
  | PAnnotation VProp VProp

data PFunctorInstance = PFunctorInstance Binder Binder Binder Binder Binder (PropClosure (A 5))
