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
  VTy,
  VProp (..),
  PFunctorInstance (..),
  Closure (..),
  Defun (..),
  PropClosure,
  ValClosure,
  ClosureEval (..),
  ClosureApply (..),
  A,
  BD (..),
  Env,
  EnvEntry (..),
  prop,
  val,
  restrict,
  applyEntry,
  level,
  extend,
  var,
  varR,
  varP,
  showElimHead,
)
where

import Syntax

import Data.Type.Nat
import Data.Void

data BD = Bound | Defined
  deriving (Show)

data EnvEntry
  = Prop VProp
  | Val Val VProp

prop :: EnvEntry -> VProp
prop (Prop p) = p
prop (Val _ p) = p

val :: EnvEntry -> Val
val (Val v _) = v
val (Prop _) = error "BUG: Tried to project value from prop entry"

restrict :: EnvEntry -> EnvEntry
restrict (Prop p) = Prop p
restrict (Val _ p) = Prop p

applyEntry :: (Val -> Val) -> (VProp -> VProp) -> EnvEntry -> EnvEntry
applyEntry _ g (Prop p) = Prop (g p)
applyEntry f g (Val v p) = Val (f v) (g p)

type Env = [(BD, EnvEntry)]

level :: Env -> Lvl
level env = Lvl (length env)

extend :: Sort -> Lvl -> Env -> Env
extend sort lvl env = env :> (Bound, var sort lvl)

data Defun cod
  = ClosureEqFun Sort cod (Closure (A 1) cod) cod
  | ClosureEqPiFamily Sort EnvEntry cod cod (Closure (A 1) cod) (Closure (A 1) cod)
  | ClosureEqPi Sort Binder cod cod (Closure (A 1) cod) (Closure (A 1) cod)
  | ClosureEqSigmaFamily EnvEntry cod cod (Closure (A 1) cod) (Closure (A 1) cod)
  | ClosureEqSigma Binder cod cod (Closure (A 1) cod) (Closure (A 1) cod)
  | ClosureEqQuotientY EnvEntry EnvEntry cod cod (Closure (A 2) cod) (Closure (A 2) cod)
  | ClosureEqQuotientX EnvEntry Binder cod cod (Closure (A 2) cod) (Closure (A 2) cod)
  | ClosureEqQuotient Binder Binder cod cod (Closure (A 2) cod) (Closure (A 2) cod)
  | ClosureEqPair Binder (Closure (A 1) cod) EnvEntry EnvEntry cod cod
  | ClosureCastPi Sort cod cod (Closure (A 1) cod) (Closure (A 1) cod) VProp cod
  | ClosureNaturalTransformation cod cod
  | ClosureFixFType Binder cod Env (Term Ix)
  | ClosureLiftViewInner (Closure (A 6) cod) EnvEntry EnvEntry EnvEntry EnvEntry
  | ClosureLiftView Binder (Closure (A 6) cod) EnvEntry EnvEntry EnvEntry

data Closure (n :: Nat) cod where
  Closure :: forall n cod. Env -> Term Ix -> Closure n cod
  Lift :: forall n cod. cod -> Closure n cod
  SubstClosure :: forall n cod. EnvEntry -> Closure ('S n) cod -> Closure ('S n) cod
  DefunBase :: forall cod. EnvEntry -> Defun cod -> Closure 'Z cod
  Defun :: forall cod. Defun cod -> Closure ('S 'Z) cod

class Monad m => ClosureEval m cod where
  closureEval :: Env -> Term Ix -> m cod
  closureDefunEval :: Defun cod -> EnvEntry -> m cod

class Monad m => ClosureApply m (n :: Nat) cl cod | cod cl -> m, m n cod -> cl where
  app :: ClosureEval m cod => Closure n cod -> cl

instance Monad m => ClosureApply m 'Z (m cod) cod where
  app (Closure env t) = closureEval env t
  app (Lift v) = pure v
  app (DefunBase v defun) = do
    closureDefunEval defun v

instance ClosureApply m n res cod => ClosureApply m ('S n) (EnvEntry -> res) cod where
  app (Closure env t) u = app @m @n @res @cod (Closure @n (env :> (Bound, u)) t)
  app (Lift v) _ = app (Lift @n v)
  app (SubstClosure v cl) _ = app cl v
  app (Defun f) u = app (DefunBase u f)

type family A n where
  A n = FromGHC n

var :: Sort -> Lvl -> EnvEntry
var Relevant lvl = Val (VVar lvl) (PVar lvl)
var Irrelevant lvl = Prop (PVar lvl)
var (SortMeta m) _ = absurd m

varR, varP :: Lvl -> EnvEntry
varR = var Relevant
varP = var Irrelevant

type VTy = Val

type ValClosure n = Closure n Val

type PropClosure n = Closure n VProp

-- Note that [~] is an eliminator for the universe, however it does not
-- have a single point on which it might block. Therefore, it cannot be an
-- eliminator in a spine
data VElim
  = VApp Val
  | VAppProp VProp
  | VNElim Binder (ValClosure (A 1)) Val Binder Binder (ValClosure (A 2))
  | VFst
  | VSnd
  | VQElim Binder (ValClosure (A 1)) Binder (ValClosure (A 1)) Binder Binder Binder (PropClosure (A 3))
  | VJ VTy Val Binder Binder (ValClosure (A 2)) Val Val
  | VBoxElim
  | VMatch Binder (ValClosure (A 1)) [(Name, Binder, Binder, ValClosure (A 2))]

showElimHead :: VElim -> String
showElimHead (VApp {}) = "<application>"
showElimHead (VAppProp {}) = "<prop-application>"
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
  | VFlex MetaVar Env
  | VU Relevance
  | VLambda Binder (ValClosure (A 1))
  | VPi Relevance Binder VTy (ValClosure (A 1))
  | VZero
  | VSucc Val
  | VNat
  | VExists Binder VTy (ValClosure (A 1))
  | VAbort VTy VProp
  | VEmpty
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
  | VBoxProof VProp
  | VBox Val
  | VROne
  | VRUnit
  | VCons Name Val VProp
  | VFLift Val Val
  | VFmap Val Val Val Val Val Val
  | VFixedPoint VTy Binder Binder Binder Binder Binder (ValClosure (A 4)) (ValClosure (A 5)) (Maybe Val)
  | VMu Tag Name VTy Binder [(Name, (Binder, ValClosure (A 2), ValClosure (A 3)))] (Maybe VFunctorInstance) (Maybe Val)

data VFunctorInstance = VFunctorInstance Binder Binder Binder Binder Binder (ValClosure (A 6))

pattern VVar :: Lvl -> Val
pattern VVar lvl = VNeutral (VRigid lvl) []

pattern VMeta :: MetaVar -> Env -> Val
pattern VMeta mv env = VNeutral (VFlex mv env) []

pattern VFun :: Relevance -> VTy -> VTy -> VTy
pattern VFun s a b = VPi s Hole a (Lift b)

pattern VAnd :: VTy -> VTy -> VTy
pattern VAnd a b = VExists Hole a (Lift b)

data VProp
  = PVar Lvl
  | PMeta MetaVar Env
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
  | PROne
  | PRUnit
  | PCons Name VProp VProp
  | PIn VProp
  | PFLift VProp VProp
  | PFmap VProp VProp VProp VProp VProp VProp
  | PMatch VProp Binder (PropClosure (A 1)) [(Name, Binder, Binder, PropClosure (A 2))]
  | PFixedPoint VProp Binder Binder Binder Binder Binder (PropClosure (A 4)) (PropClosure (A 5))
  | PMu Tag Name VProp Binder [(Name, Binder, PropClosure (A 2), PropClosure (A 3))] (Maybe PFunctorInstance)
  | PLet Binder Sort VProp VProp (PropClosure (A 1))
  | PAnnotation VProp VProp

data PFunctorInstance = PFunctorInstance Binder Binder Binder Binder Binder (PropClosure (A 6))
