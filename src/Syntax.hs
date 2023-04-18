{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Syntax (
  pattern (:>),
  (++:>),
  Name,
  Binder (..),
  Loc (..),
  Ix (..),
  Lvl (..),
  lvl2ix,
  MetaVar (..),
  RelevanceF (..),
  Relevance,
  pattern SortHole,
  ULevel,
  TermF (..),
  Term,
  Type,
  RawF (..),
  Raw,
  pattern R,
  pattern HoleF,
  pattern Var,
  pattern U,
  pattern Lambda,
  pattern App,
  pattern Pi,
  pattern Zero,
  pattern Succ,
  pattern NElim,
  pattern Nat,
  pattern PropPair,
  pattern PropFst,
  pattern PropSnd,
  pattern Exists,
  pattern Abort,
  pattern Empty,
  pattern One,
  pattern Unit,
  pattern Eq,
  pattern Refl,
  pattern Sym,
  pattern Trans,
  pattern Ap,
  pattern Transp,
  pattern Cast,
  pattern Pair,
  pattern Fst,
  pattern Snd,
  pattern Sigma,
  pattern Quotient,
  pattern QProj,
  pattern QElim,
  pattern IdRefl,
  pattern IdPath,
  pattern J,
  pattern Id,
  pattern BoxProof,
  pattern BoxElim,
  pattern Box,
  pattern Cons,
  pattern Match,
  pattern FixedPoint,
  pattern Mu,
  pattern Let,
  pattern Annotation,
  pattern Meta,
  VElim (..),
  VSpine,
  VProp (..),
  ($$$),
  Val (..),
  pattern VVar,
  pattern VMeta,
  pattern VFun,
  pattern VAnd,
  VTy,
  PushArgument (..),
  Closure (..),
  ClosureApply (..),
  appVector,
  appVectorFull,
  appOne,
  A,
  BD (..),
  Env,
  level,
  -- varMap,
  VarShowable (..),
  prettyPrintTerm,
  prettyPrintTermDebug,
  showElimHead,
  -- eraseSourceLocations
)
where

import Vector qualified as V

import Data.Fix hiding (Mu)
import Data.Type.Equality qualified as E
import Data.Type.Nat
import Data.Void
import Error.Diagnose.Position (Position (..))

import Text.Printf (IsChar (toChar))

-- Snoc lists
infixl 4 :>
pattern (:>) :: [a] -> a -> [a]
pattern xs :> x = x : xs

{-# COMPLETE (:>), [] #-}

infixl 4 ++:>
(++:>) :: [a] -> [a] -> [a]
xs ++:> [] = xs
xs ++:> (y : ys) = (xs :> y) ++:> ys

-- Language source identifiers
type Name = String
data Binder
  = Name Name
  | Hole

instance Show Binder where
  show (Name n) = n
  show Hole = "_"

-- Syntactic element tagged with a source code location
data Loc a = L
  { location :: Position
  , syntax :: a
  }

instance Show a => Show (Loc a) where
  showsPrec prec = showsPrec prec . syntax

instance Functor Loc where
  fmap f (L l s) = L l (f s)

-- Internal de Bruijn indices
newtype Ix = Ix Int
  deriving (Eq, Ord, Show, Num, Enum)

-- Internal de Bruijn levels
newtype Lvl = Lvl Int
  deriving (Eq, Ord, Show, Num, Enum)

lvl2ix :: Lvl -> Lvl -> Ix
lvl2ix (Lvl l) (Lvl x) = Ix (l - x - 1)

newtype MetaVar = MetaVar Int
  deriving (Eq, Ord, Num)

instance Show MetaVar where
  show (MetaVar v) = "?" ++ show v

-- Universe levels
type ULevel = Int

-- Relevance of a universe.
-- OTT universes may either be proof-relevant, or proof-irrelevant.
data RelevanceF meta
  = Relevant
  | Irrelevant
  | SortMeta meta
  deriving (Eq)

instance {-# OVERLAPS #-} Show (RelevanceF ()) where
  show Relevant = "U"
  show Irrelevant = "Ω"
  show (SortMeta ()) = "_"

instance Show meta => Show (RelevanceF meta) where
  show Relevant = "U"
  show Irrelevant = "Ω"
  show (SortMeta m) = show m

pattern SortHole :: RelevanceF ()
pattern SortHole = SortMeta ()

{-# COMPLETE Relevant, Irrelevant, SortHole #-}

type Relevance = RelevanceF MetaVar

data TermF proj meta v t
  = VarF v
  | -- Universe terms have a relevance and a level
    UF (RelevanceF meta)
  | LambdaF Binder t
  | AppF t t
  | -- Pi types are annotated with their domain type's relevance and level, and the co-domain level
    PiF (RelevanceF meta) Binder t t
  | ZeroF
  | SuccF t
  | NElimF Binder t t Binder Binder t t
  | NatF
  | PropPairF t t
  | FstF proj t
  | SndF proj t
  | -- Existential types are annotated with their domain and co-domain levels
    ExistsF Binder t t
  | AbortF t t
  | EmptyF
  | OneF
  | UnitF
  | -- Observational equality type t ~A u
    EqF t t t
  | ReflF t
  | -- Extra axioms for symmetry, transitivity and congruence of observational equality
    -- One of the benefits of TTobs is we can add true axioms to Prop without changing
    -- normalisation behaviour
    SymF t t t
  | TransF t t t t t
  | ApF t Binder t t t t
  | -- Transport a value along a proof of equality
    TranspF t Binder Binder t t t t
  | -- Type casting
    CastF t t t t
  | -- Sigma Types
    PairF t t
  | SigmaF Binder t t
  | -- Quotient Types
    -- A / (x x'. R, x. Refl, x y xy. Sym, x y z xy yz. Trans) : U
    QuotientF t Binder Binder t Binder t Binder Binder Binder t Binder Binder Binder Binder Binder t
  | QProjF t
  | -- Q-elim(z. B, x. tπ, x y e. t~, u) : B[z/u]
    QElimF Binder t Binder t Binder Binder Binder t t
  | -- Inductive equality
    IdReflF t
  | IdPathF t
  | JF t t Binder Binder t t t t
  | IdF t t t
  | BoxProofF t
  | BoxElimF t
  | BoxF t
  | ConsF Name t
  | MatchF t Binder t [(Name, Binder, t)]
  | FixedPointF t Binder Binder Binder Binder t t
  | MuF Binder t Binder [(Name, t)]
  | -- Annotations
    LetF Binder t t t
  | AnnotationF t t
  | MetaF meta

newtype RawF t = RawF (Loc (TermF () () Name t))

type Raw = Fix RawF

pattern R :: Position -> TermF () () Name Raw -> Raw
pattern R sl term = Fix (RawF (L sl term))

pattern HoleF :: TermF () () Name t
pattern HoleF = MetaF ()

{-# COMPLETE R #-}

type Term v = Fix (TermF (RelevanceF Void) MetaVar v)

type Type v = Term v

pattern Var :: v -> Term v
pattern Var x = Fix (VarF x)

pattern U :: Relevance -> Term v
pattern U s = Fix (UF s)

pattern Lambda :: Binder -> Term v -> Term v
pattern Lambda x e = Fix (LambdaF x e)

pattern App :: Term v -> Term v -> Term v
pattern App t u = Fix (AppF t u)

pattern Pi :: Relevance -> Binder -> Type v -> Type v -> Type v
pattern Pi s x a b = Fix (PiF s x a b)

pattern Zero :: Term v
pattern Zero = Fix ZeroF

pattern Succ :: Term v -> Term v
pattern Succ n = Fix (SuccF n)

pattern NElim :: Binder -> Term v -> Term v -> Binder -> Binder -> Term v -> Term v -> Term v
pattern NElim z a t0 x ih ts n = Fix (NElimF z a t0 x ih ts n)

pattern Nat :: Term v
pattern Nat = Fix NatF

pattern PropPair :: Term v -> Term v -> Term v
pattern PropPair t u = Fix (PropPairF t u)

pattern PropFst :: Term v -> Term v
pattern PropFst p = Fix (FstF Irrelevant p)

pattern PropSnd :: Term v -> Term v
pattern PropSnd p = Fix (SndF Irrelevant p)

pattern Exists :: Binder -> Term v -> Term v -> Term v
pattern Exists x a b = Fix (ExistsF x a b)

pattern Abort :: Type v -> Term v -> Term v
pattern Abort a t = Fix (AbortF a t)

pattern Empty :: Term v
pattern Empty = Fix EmptyF

pattern One :: Term v
pattern One = Fix OneF

pattern Unit :: Term f
pattern Unit = Fix UnitF

pattern Eq :: Term v -> Type v -> Term v -> Term v
pattern Eq t a u = Fix (EqF t a u)

pattern Refl :: Term v -> Term v
pattern Refl t = Fix (ReflF t)

pattern Sym :: Term v -> Term v -> Term v -> Term v
pattern Sym t u e = Fix (SymF t u e)

pattern Trans :: Term v -> Term v -> Term v -> Term v -> Term v -> Term v
pattern Trans t u v e e' = Fix (TransF t u v e e')

pattern Ap :: Type v -> Binder -> Term v -> Term v -> Term v -> Term v -> Term v
pattern Ap b x t u v e = Fix (ApF b x t u v e)

pattern Transp :: Term v -> Binder -> Binder -> Term v -> Term v -> Term v -> Term v -> Term v
pattern Transp t x pf b u t' e = Fix (TranspF t x pf b u t' e)

pattern Cast :: Type v -> Type v -> Term v -> Term v -> Term v
pattern Cast a b e t = Fix (CastF a b e t)

pattern Pair :: Term v -> Term v -> Term v
pattern Pair t u = Fix (PairF t u)

pattern Fst :: Term v -> Term v
pattern Fst p = Fix (FstF Relevant p)

pattern Snd :: Term v -> Term v
pattern Snd p = Fix (SndF Relevant p)

pattern Sigma :: Binder -> Type v -> Type v -> Type v
pattern Sigma x a b = Fix (SigmaF x a b)

pattern Quotient
  :: Type v -- Base type          [A]
  -> Binder
  -> Binder
  -> Type v -- Quotient relation  [R : A -> A -> Ω]
  -> Binder
  -> Term v -- Reflexivity proof  [Rr : (x : A) -> R x x]
  -> Binder
  -> Binder
  -> Binder
  -> Term v -- Symmetry proof     [Rs : (x, y : A) -> R x y -> R y x]
  -> Binder
  -> Binder
  -> Binder
  -> Binder
  -> Binder
  -> Term v -- Transitivity proof [Rt : (x, y, z : A) -> R x y -> R y z -> R x z]
  -> Term v -- Quotient type      [A/(R, Rr, Rs, Rt)]
pattern Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt =
  Fix (QuotientF a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt)

pattern QProj :: Term v -> Term v
pattern QProj t = Fix (QProjF t)

pattern QElim
  :: Binder
  -> Type v -- Type family        [B : A/R -> s]
  -> Binder
  -> Term v -- Function           [tπ : (x : A) -> B π(x)]
  -> Binder
  -> Binder
  -> Binder
  -> Type v -- Preservation proof [t~ : (x, y : A) -> (e : R x y) -> (tπ x) ~[B π(x)] cast(B π(y), B π(x), B e, tπ y)]
  -> Term v -- Argument           [u : A/R]
  -> Term v -- Eliminated term    [Q-elim(B, tπ, t~, u) : B u]
pattern QElim z b x tpi px py pe p u = Fix (QElimF z b x tpi px py pe p u)

pattern IdRefl :: Term v -> Term v
pattern IdRefl t = Fix (IdReflF t)

pattern IdPath :: Term v -> Term v
pattern IdPath t = Fix (IdPathF t)

pattern J :: Type v -> Term v -> Binder -> Binder -> Type v -> Term v -> Term v -> Term v -> Term v
pattern J a t x pf b u t' e = Fix (JF a t x pf b u t' e)

pattern Id :: Type v -> Term v -> Term v -> Type v
pattern Id a t u = Fix (IdF a t u)

pattern BoxProof :: Term v -> Term v
pattern BoxProof e = Fix (BoxProofF e)

pattern BoxElim :: Term v -> Term v
pattern BoxElim t = Fix (BoxElimF t)

pattern Box :: Type v -> Type v
pattern Box a = Fix (BoxF a)

pattern Cons :: Name -> Term v -> Term v
pattern Cons c t = Fix (ConsF c t)

pattern Match :: Term v -> Binder -> Type v -> [(Name, Binder, Term v)] -> Term v
pattern Match t x p bs = Fix (MatchF t x p bs)

pattern FixedPoint :: Type v -> Binder -> Binder -> Binder -> Binder -> Type v -> Term v -> Term v
pattern FixedPoint i g f p x c t = Fix (FixedPointF i g f p x c t)

pattern Mu :: Binder -> Type v -> Binder -> [(Name, Type v)] -> Type v
pattern Mu f t x cs = Fix (MuF f t x cs)

pattern Let :: Binder -> Type v -> Term v -> Term v -> Term v
pattern Let x a t u = Fix (LetF x a t u)

pattern Annotation :: Term v -> Type v -> Term v
pattern Annotation t a = Fix (AnnotationF t a)

pattern Meta :: MetaVar -> Term v
pattern Meta v = Fix (MetaF v)

{-# COMPLETE
  Var
  , U
  , Lambda
  , App
  , Pi
  , Zero
  , Succ
  , NElim
  , Nat
  , PropPair
  , PropFst
  , PropSnd
  , Exists
  , Abort
  , Empty
  , One
  , Unit
  , Eq
  , Refl
  , Sym
  , Trans
  , Ap
  , Transp
  , Cast
  , Pair
  , Fst
  , Snd
  , Sigma
  , Quotient
  , QProj
  , QElim
  , IdRefl
  , IdPath
  , J
  , Id
  , BoxProof
  , BoxElim
  , Box
  , Cons
  , Match
  , FixedPoint
  , Mu
  , Let
  , Annotation
  , Meta
  #-}

instance Functor (TermF p m v) where
  fmap _ (VarF x) = VarF x
  fmap _ (UF s) = UF s
  fmap f (LambdaF x e) = LambdaF x (f e)
  fmap f (AppF t u) = AppF (f t) (f u)
  fmap f (PiF s x a b) = PiF s x (f a) (f b)
  fmap _ ZeroF = ZeroF
  fmap f (SuccF n) = SuccF (f n)
  fmap f (NElimF z a t0 x ih ts n) = NElimF z (f a) (f t0) x ih (f ts) (f n)
  fmap _ NatF = NatF
  fmap f (PropPairF t u) = PropPairF (f t) (f u)
  fmap f (FstF s p) = FstF s (f p)
  fmap f (SndF s p) = SndF s (f p)
  fmap f (ExistsF x a b) = ExistsF x (f a) (f b)
  fmap f (AbortF a t) = AbortF (f a) (f t)
  fmap _ EmptyF = EmptyF
  fmap _ OneF = OneF
  fmap _ UnitF = UnitF
  fmap f (EqF t a u) = EqF (f t) (f a) (f u)
  fmap f (ReflF t) = ReflF (f t)
  fmap f (SymF t u e) = SymF (f t) (f u) (f e)
  fmap f (TransF t u v e e') = TransF (f t) (f u) (f v) (f e) (f e')
  fmap f (ApF b x t u v e) = ApF (f b) x (f t) (f u) (f v) (f e)
  fmap f (TranspF t x pf b u t' e) = TranspF (f t) x pf (f b) (f u) (f t') (f e)
  fmap f (CastF a b e t) = CastF (f a) (f b) (f e) (f t)
  fmap f (PairF t u) = PairF (f t) (f u)
  fmap f (SigmaF x a b) = SigmaF x (f a) (f b)
  fmap f (QuotientF a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) =
    QuotientF (f a) x y (f r) rx (f rr) sx sy sxy (f rs) tx ty tz txy tyz (f rt)
  fmap f (QProjF t) = QProjF (f t)
  fmap f (QElimF z b x tpi px py pe p u) = QElimF z (f b) x (f tpi) px py pe (f p) (f u)
  fmap f (IdReflF t) = IdReflF (f t)
  fmap f (IdPathF t) = IdPathF (f t)
  fmap f (JF a t x pf b u t' e) = JF (f a) (f t) x pf (f b) (f u) (f t') (f e)
  fmap f (IdF a t u) = IdF (f a) (f t) (f u)
  fmap f (BoxProofF e) = BoxProofF (f e)
  fmap f (BoxElimF t) = BoxElimF (f t)
  fmap f (BoxF a) = BoxF (f a)
  fmap f (ConsF c t) = ConsF c (f t)
  fmap f (MatchF t x p bs) = MatchF (f t) x (f p) (fmap (fmap f) bs)
  fmap f (FixedPointF i g f' p x c t) = FixedPointF (f i) g f' p x (f c) (f t)
  fmap f (MuF g t x cs) = MuF g (f t) x (fmap (fmap f) cs)
  fmap f (LetF x a t u) = LetF x (f a) (f t) (f u)
  fmap f (AnnotationF t a) = AnnotationF (f t) (f a)
  fmap _ (MetaF m) = MetaF m

instance Foldable (TermF p m v) where
  foldr _ e (VarF _) = e
  foldr _ e (UF _) = e
  foldr f e (LambdaF _ t) = f t e
  foldr f e (AppF t u) = (f t . f u) e
  foldr f e (PiF _ _ a b) = (f a . f b) e
  foldr _ e ZeroF = e
  foldr f e (SuccF n) = f n e
  foldr f e (NElimF _ a t0 _ _ ts n) = (f a . f t0 . f ts . f n) e
  foldr _ e NatF = e
  foldr f e (PropPairF t u) = (f t . f u) e
  foldr f e (FstF _ p) = f p e
  foldr f e (SndF _ p) = f p e
  foldr f e (ExistsF _ a b) = (f a . f b) e
  foldr f e (AbortF a t) = (f a . f t) e
  foldr _ e EmptyF = e
  foldr _ e OneF = e
  foldr _ e UnitF = e
  foldr f e (EqF t a u) = (f t . f a . f u) e
  foldr f e (ReflF t) = f t e
  foldr f e (SymF t u e') = (f t . f u . f e') e
  foldr f e (TransF t u v e' e'') = (f t . f u . f v . f e' . f e'') e
  foldr f e (ApF b _ t u v e') = (f b . f t . f u . f v . f e') e
  foldr f e (TranspF t _ _ b u t' v) = (f t . f b . f u . f t' . f v) e
  foldr f e (CastF a b u t) = (f a . f b . f u . f t) e
  foldr f e (PairF t u) = (f t . f u) e
  foldr f e (SigmaF _ a b) = (f a . f b) e
  foldr f e (QuotientF a _ _ r _ rr _ _ _ rs _ _ _ _ _ rt) = (f a . f r . f rr . f rs . f rt) e
  foldr f e (QProjF t) = f t e
  foldr f e (QElimF _ b _ tpi _ _ _ p u) = (f b . f tpi . f p . f u) e
  foldr f e (IdReflF t) = f t e
  foldr f e (IdPathF t) = f t e
  foldr f e (JF a t _ _ b u t' v) = (f a . f t . f b . f u . f t' . f v) e
  foldr f e (IdF a t u) = (f a . f t . f u) e
  foldr f e (BoxProofF t) = f t e
  foldr f e (BoxElimF t) = f t e
  foldr f e (BoxF a) = f a e
  foldr f e (ConsF _ t) = f t e
  foldr f e (MatchF t _ p bs) = (f t . f p) (foldr (\(_, _, b) e -> f b e) e bs)
  foldr f e (FixedPointF i _ _ _ _ c t) = (f i . f c . f t) e
  foldr f e (MuF _ t _ cs) = f t (foldr (\(_, b) e -> f b e) e cs)
  foldr f e (LetF _ a t u) = (f a . f t . f u) e
  foldr f e (AnnotationF t a) = (f t . f a) e
  foldr _ e (MetaF _) = e

instance Traversable (TermF p m v) where
  traverse _ (VarF x) = pure (VarF x)
  traverse _ (UF s) = pure (UF s)
  traverse f (LambdaF x e) = LambdaF x <$> f e
  traverse f (AppF t u) = AppF <$> f t <*> f u
  traverse f (PiF s x a b) = PiF s x <$> f a <*> f b
  traverse _ ZeroF = pure ZeroF
  traverse f (SuccF n) = SuccF <$> f n
  traverse f (NElimF z a t0 x ih ts n) = NElimF z <$> f a <*> f t0 <*> pure x <*> pure ih <*> f ts <*> f n
  traverse _ NatF = pure NatF
  traverse f (PropPairF t u) = PropPairF <$> f t <*> f u
  traverse f (FstF s p) = FstF s <$> f p
  traverse f (SndF s p) = SndF s <$> f p
  traverse f (ExistsF x a b) = ExistsF x <$> f a <*> f b
  traverse f (AbortF a t) = AbortF <$> f a <*> f t
  traverse _ EmptyF = pure EmptyF
  traverse _ OneF = pure OneF
  traverse _ UnitF = pure UnitF
  traverse f (EqF t a u) = EqF <$> f t <*> f a <*> f u
  traverse f (ReflF t) = ReflF <$> f t
  traverse f (SymF t u e) = SymF <$> f t <*> f u <*> f e
  traverse f (TransF t u v e e') = TransF <$> f t <*> f u <*> f v <*> f e <*> f e'
  traverse f (ApF b x t u v e) = ApF <$> f b <*> pure x <*> f t <*> f u <*> f v <*> f e
  traverse f (TranspF t x pf b u t' e) =
    TranspF <$> f t <*> pure x <*> pure pf <*> f b <*> f u <*> f t' <*> f e
  traverse f (CastF a b e t) = CastF <$> f a <*> f b <*> f e <*> f t
  traverse f (PairF t u) = PairF <$> f t <*> f u
  traverse f (SigmaF x a b) = SigmaF x <$> f a <*> f b
  traverse f (QuotientF a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) =
    QuotientF <$> f a <*> pure x <*> pure y <*> f r <*> pure rx <*> f rr <*> pure sx <*> pure sy <*> pure sxy <*> f rs <*> pure tx <*> pure ty <*> pure tz <*> pure txy <*> pure tyz <*> f rt
  traverse f (QProjF t) = QProjF <$> f t
  traverse f (QElimF z b x tpi px py pe p u) =
    QElimF z <$> f b <*> pure x <*> f tpi <*> pure px <*> pure py <*> pure pe <*> f p <*> f u
  traverse f (IdReflF t) = IdReflF <$> f t
  traverse f (IdPathF t) = IdPathF <$> f t
  traverse f (JF a t x pf b u t' e) =
    JF <$> f a <*> f t <*> pure x <*> pure pf <*> f b <*> f u <*> f t' <*> f e
  traverse f (IdF a t u) = IdF <$> f a <*> f t <*> f u
  traverse f (BoxProofF e) = BoxProofF <$> f e
  traverse f (BoxElimF t) = BoxElimF <$> f t
  traverse f (BoxF a) = BoxF <$> f a
  traverse f (ConsF c t) = ConsF c <$> f t
  traverse f (MatchF t x p bs) = MatchF <$> f t <*> pure x <*> f p <*> traverse (\(c, x, t) -> (c,x,) <$> f t) bs
  traverse f (FixedPointF i g f' p x c t) = FixedPointF <$> f i <*> pure g <*> pure f' <*> pure p <*> pure x <*> f c <*> f t
  traverse f (MuF g t x cs) = MuF g <$> f t <*> pure x <*> traverse (\(c, b) -> (c,) <$> f b) cs
  traverse f (LetF x a t u) = LetF x <$> f a <*> f t <*> f u
  traverse f (AnnotationF t a) = AnnotationF <$> f t <*> f a
  traverse _ (MetaF m) = pure (MetaF m)

instance Functor RawF where
  fmap f (RawF t) = RawF (L {location = location t, syntax = fmap f (syntax t)})

-- varMap :: forall v v'. (v -> v') -> Term v -> Term v'
-- varMap f = foldFix alg
--   where
--     alg :: TermF (RelevanceF Void) MetaVar v (Term v') -> Term v'
--     alg (VarF x) = Var (f x)
--     alg (UF s) = U s
--     alg (LambdaF x e) = Lambda x e
--     alg (AppF t u) = App t u
--     alg (PiF s x a b) = Pi s x a b
--     alg ZeroF = Zero
--     alg (SuccF n) = Succ n
--     alg (NElimF z a t0 x ih ts n) = NElim z a t0 x ih ts n
--     alg NatF = Nat
--     alg (PropPairF t u) = PropPair t u
--     alg (FstF Irrelevant p) = PropFst p
--     alg (SndF Irrelevant p) = PropSnd p
--     alg (ExistsF x a b) = Exists x a b
--     alg (AbortF a t) = Abort a t
--     alg EmptyF = Empty
--     alg OneF = One
--     alg UnitF = Unit
--     alg (EqF t a u) = Eq t a u
--     alg (ReflF t) = Refl t
--     alg (SymF t u e) = Sym t u e
--     alg (TransF t u v e e') = Trans t u v e e'
--     alg (ApF b x t u v e) = Ap b x t u v e
--     alg (TranspF t x pf b u t' e) = Transp t x pf b u t' e
--     alg (CastF a b e t) = Cast a b e t
--     alg (PairF t u) = Pair t u
--     alg (FstF Relevant p) = Fst p
--     alg (SndF Relevant p) = Snd p
--     alg (SigmaF x a b) = Sigma x a b
--     alg (QuotientF a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) =
--       Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt
--     alg (QProjF t) = QProj t
--     alg (QElimF z b x tpi px py pe p u) = QElim z b x tpi px py pe p u
--     alg (IdReflF t) = IdRefl t
--     alg (IdPathF t) = IdPath t
--     alg (JF a t x pf b u t' e) = J a t x pf b u t' e
--     alg (IdF a t u) = Id a t u
--     alg (LetF x a t u) = Let x a t u
--     alg (AnnotationF t a) = Annotation t a
--     alg (MetaF m) = Meta m
--     -- To make GHC happy
--     alg (FstF (SortMeta v) _) = absurd v
--     alg (SndF (SortMeta v) _) = absurd v

precAtom, precApp, precPi, precLet :: Int
precAtom = 3
precApp = 2
precPi = 1
precLet = 0

class VarShowable v where
  showsVar :: v -> [Binder] -> ShowS

instance VarShowable Ix where
  showsVar (Ix x) ns = shows (ns !! x)

instance IsChar s => VarShowable [s] where
  showsVar x _ = showString (fmap toChar x)

prettyPrintTerm :: VarShowable v => [Binder] -> Term v -> String
prettyPrintTerm = prettyPrintTermDebug False

prettyPrintTermDebug :: forall v. VarShowable v => Bool -> [Binder] -> Term v -> String
prettyPrintTermDebug debug names tm = go 0 names tm []
  where
    par :: Int -> Int -> ShowS -> ShowS
    par p p' = showParen (p' < p || debug)

    str :: String -> ShowS
    str = showString

    chr :: Char -> ShowS
    chr = showChar

    binder :: Binder -> ShowS
    binder = shows

    -- showRelevance :: Relevance -> ShowS
    -- showRelevance Relevant = chr 'U'
    -- showRelevance Irrelevant = chr 'Ω'

    comma, dot, space :: ShowS
    comma = str ", "
    dot = str ". "
    space = chr ' '

    sep :: ShowS -> [ShowS] -> ShowS
    sep _ [] = id
    sep _ [x] = x
    sep sepWith (x : xs) = x . sepWith . sep sepWith xs

    tag :: String -> ShowS
    tag t
      | debug = chr '{' . str t . chr '}'
      | otherwise = id

    go :: Int -> [Binder] -> Term v -> ShowS
    go _ ns (Var x) = tag "V" . showsVar x ns
    go _ _ (U s) = shows s
    go prec ns (Lambda x e) =
      let domain = chr 'λ' . binder x
       in par prec precLet (domain . dot . go precLet (ns :> x) e)
    go prec ns (App t u) =
      tag "A" . par prec precApp (go precApp ns t . space . go precAtom ns u)
    go prec ns (Pi _ Hole a b) =
      let domain = go precApp ns a
          codomain = go precPi (ns :> Hole) b
       in tag "Π" . par prec precPi (domain . str " → " . codomain)
    go prec ns (Pi s x a b) =
      let domain = showParen True (binder x . str " :" . shows s . space . go precLet ns a)
          codomain = go precPi (ns :> x) b
       in tag "Π" . par prec precPi (domain . str " → " . codomain)
    go _ _ Zero = chr '0'
    go prec ns (Succ n) = par prec precApp (str "S " . go precAtom ns n)
    go prec ns (NElim z a t0 x ih ts n) =
      let a' = binder z . dot . go precLet (ns :> z) a
          t0' = go precLet ns t0
          ts' = binder x . space . binder ih . dot . go precLet (ns :> x :> ih) ts
          n' = go precLet ns n
       in par prec precApp (str "ℕ-elim" . showParen True (sep comma [a', t0', ts', n']))
    go _ _ Nat = chr 'ℕ'
    go _ ns (PropPair t u) = chr '⟨' . go precLet ns t . comma . go precLet ns u . chr '⟩'
    go prec ns (PropFst p) = par prec precApp (str "fst " . go precAtom ns p)
    go prec ns (PropSnd p) = par prec precApp (str "snd " . go precAtom ns p)
    go prec ns (Exists Hole a b) =
      let domain = go precApp ns a
          codomain = go precApp (ns :> Hole) b
       in tag "∃" . par prec precPi (domain . str " ∧ " . codomain)
    go prec ns (Exists x a b) =
      let domain = showParen True (binder x . str " : " . go precLet ns a)
          codomain = go precPi (ns :> x) b
       in par prec precPi (chr '∃' . domain . dot . codomain)
    go prec ns (Abort a t) =
      let a' = go precLet ns a
          t' = go precLet ns t
       in par prec precApp (str "⊥-elim" . showParen True (a' . comma . t'))
    go _ _ Empty = chr '⊥'
    go _ _ One = chr '*'
    go _ _ Unit = chr '⊤'
    go prec ns (Eq t a u) =
      par prec precPi (go precApp ns t . str " ~[" . go precLet ns a . str "] " . go precApp ns u)
    go prec ns (Refl t) = par prec precApp (str "refl " . go precAtom ns t)
    go prec ns (Sym t u e) =
      let go' = go precLet ns
       in par prec precApp (str "sym" . showParen True (sep comma [go' t, go' u, go' e]))
    go prec ns (Trans t u v e e') =
      let go' = go precLet ns
       in par prec precApp (str "trans" . showParen True (sep comma [go' t, go' u, go' v, go' e, go' e']))
    go prec ns (Ap b x t u v e) =
      let t' = binder x . dot . go precLet (ns :> x) t
          go' = go precLet ns
       in par prec precApp (str "ap" . showParen True (sep comma [go' b, t', go' u, go' v, go' e]))
    go prec ns (Transp t x pf b u v e) =
      let t' = go precLet ns t
          b' = binder x . space . binder pf . dot . go precLet (ns :> x :> pf) b
          u' = go precLet ns u
          v' = go precLet ns v
          e' = go precLet ns e
       in par prec precApp (str "transp" . showParen True (sep comma [t', b', u', v', e']))
    go prec ns (Cast a b e t) =
      let a' = go precLet ns a
          b' = go precLet ns b
          e' = go precLet ns e
          t' = go precLet ns t
       in par prec precApp (str "cast" . showParen True (sep comma [a', b', e', t']))
    go _ ns (Pair t u) = chr '(' . go precLet ns t . str "; " . go precLet ns u . chr ')'
    go prec ns (Fst p) = par prec precApp (str "fst " . go precAtom ns p)
    go prec ns (Snd p) = par prec precApp (str "snd " . go precAtom ns p)
    go prec ns (Sigma Hole a b) =
      let domain = go precApp ns a
          codomain = go precApp (ns :> Hole) b
       in par prec precPi (domain . str " × " . codomain)
    go prec ns (Sigma x a b) =
      let domain = chr 'Σ' . showParen True (binder x . str " : " . go precLet ns a)
          codomain = go precPi (ns :> x) b
       in tag "Σ" . par prec precPi (domain . dot . codomain)
    go prec ns (Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) =
      let a' = go precAtom ns a
          r' = binder x . space . binder y . dot . go precLet (ns :> x :> y) r
          rr' = binder rx . dot . go precLet (ns :> rx) rr
          rs' = sep space [binder sx, binder sy, binder sxy] . dot . go precLet (ns :> sx :> sy :> sxy) rs
          rt' = sep space [binder tx, binder ty, binder tz, binder txy, binder tyz] . dot . go precLet (ns :> tx :> ty :> tz :> txy :> tyz) rt
       in par prec precPi (a' . str "/(" . sep comma [r', rr', rs', rt'] . chr ')')
    go prec ns (QProj t) = par prec precApp (str "π " . go precAtom ns t)
    go prec ns (QElim z b x tpi px py pe p u) =
      let b' = binder z . dot . go precLet (ns :> z) b
          tpi' = binder x . dot . go precLet (ns :> x) tpi
          p' = sep space [binder px, binder py, binder pe] . dot . go precLet (ns :> px :> py :> pe) p
          u' = go precLet ns u
       in par prec precApp (str "Q-elim(" . sep comma [b', tpi', p', u'] . chr ')')
    go prec ns (IdRefl t) = par prec precApp (str "Idrefl " . go precAtom ns t)
    go prec ns (IdPath t) = par prec precApp (str "Idpath " . go precAtom ns t)
    go prec ns (J a t x pf b u v e) =
      let a' = go precLet ns a
          t' = go precLet ns t
          b' = binder x . space . binder pf . dot . go precLet (ns :> x :> pf) b
          u' = go precLet ns u
          v' = go precLet ns v
          e' = go precLet ns e
       in par prec precApp (str "J" . showParen True (sep comma [a', t', b', u', v', e']))
    go prec ns (Id a t u) =
      par prec precApp (str "Id" . showParen True (sep comma [go precLet ns a, go precLet ns t, go precLet ns u]))
    go prec ns (BoxProof e) =
      par prec precApp (str "◇" . go precAtom ns e)
    go prec ns (BoxElim t) =
      par prec precApp (str "▢-elim(" . go precLet ns t . chr ')')
    go prec ns (Box a) =
      par prec precApp (str "▢" . go precAtom ns a)
    go prec ns (Cons c t) =
      par prec precApp (str c . space . go precAtom ns t)
    go prec ns (Match t x p bs) =
      let t' = go precLet ns t
          p' = go precLet (ns :> x) p
          bs' = foldr ((.) . (str "\n" .) . branch) id bs
       in par prec precLet (str "match " . t' . str " as " . binder x . str " return " . p' . str " with" . bs')
      where
        branch :: (Name, Binder, Term v) -> ShowS
        branch (cons, x, t) = str "| " . str cons . str " " . binder x . str " -> " . go precLet (ns :> x) t
    go prec ns (FixedPoint i g f p x c t) =
      let i' = go precLet ns i . str " as " . binder g
          -- args = sep space (fmap binder (f : ps ++ [x]))
          args = sep space (fmap binder [f, p, x])
          c' = go precLet (ns :> g :> p :> x) c
          t' = go precLet (ns :> g :> f :> p :> x) t
       in par prec precLet (str "fix [" . i' . str "] " . args . str " : " . c' . str " = " . t')
    go prec ns (Mu f t x cs) =
      let x' = str "λ" . binder x
          cs' = chr '[' . sep (str "; ") (fmap showCons cs) . chr ']'
       in par prec precLet (str "μ" . binder f . str " : " . go precLet ns t . dot . x' . dot . cs')
      where
        showCons :: (Name, Type v) -> ShowS
        showCons (c, b) = str c . str " : " . go precLet (ns :> f :> x) b
    go prec ns (Let x a t u) =
      let a' = go precLet ns a
          t' = go precLet ns t
          u' = go precLet (ns :> x) u
       in par
            prec
            precLet
            ( str "let "
                . binder x
                . str " : "
                . a'
                . str " =\n    "
                . t'
                . str "\nin\n"
                . u'
            )
    go _ ns (Annotation t a) =
      showParen True (go precLet ns t . str " : " . go precLet ns a)
    go _ _ (Meta (MetaVar m)) = str "?" . shows m

-- eraseSourceLocations :: Raw -> Term Name
-- eraseSourceLocations = foldFix alg
--   where
--     alg :: RawF (Term Name) -> Term Name
--     alg (RawF l) = Fix (syntax l)

data BD = Bound | Defined
  deriving (Show)

type Env v = [(BD, Val v)]

level :: Env v -> Lvl
level env = Lvl (length env)

class Applicative f => PushArgument f where
  push :: (a -> f b) -> f (a -> b)

data Closure (n :: Nat) v where
  Closure :: forall n v. Env v -> Term v -> Closure n v
  Lift :: forall n v. Val v -> Closure n v
  LiftClosure :: forall n v. Closure n v -> Closure ('S n) v
  Function :: forall n v. (Val v -> Closure n v) -> Closure ('S n) v

class Applicative f => ClosureApply f (n :: Nat) cl v | cl -> v, cl -> f where
  app :: (Env v -> Term v -> f (Val v)) -> Closure n v -> cl
  makeFnClosure :: PushArgument f => cl -> f (Closure n v)

instance Applicative f => ClosureApply f 'Z (f (Val v)) v where
  app eval (Closure env t) = eval env t
  app _ (Lift v) = pure v

  makeFnClosure v = Lift <$> v

instance ClosureApply f n res v => ClosureApply f ('S n) (Val v -> res) v where
  app eval (Closure env t) u = app eval (Closure @n @v (env :> (Bound, u)) t)
  app eval (Lift v) _ = app eval (Lift @n @v v)
  app eval (LiftClosure cl) _ = app eval cl
  app eval (Function f) u = app eval (f u)

  makeFnClosure f = Function <$> push (makeFnClosure . f)

newtype VectorApp f v (n :: Nat) (m :: Nat) = VectorApp
  { runVectorApp :: Closure (Plus n m) v -> V.Vec m (Val v) -> f (Closure n v)
  }

appVectorBase :: forall f n v. (Applicative f, SNatI n) => VectorApp f v n 'Z
appVectorBase =
  case proofPlusNZero @n of
    E.Refl -> VectorApp app'
  where
    app' :: Closure n v -> V.Vec 'Z (Val v) -> f (Closure n v)
    app' cl V.Nil = pure cl

appVectorInd
  :: forall m k f v
   . (SNatI m, SNatI k)
  => (VectorApp f v k m -> VectorApp f v k ('S m))
appVectorInd (VectorApp recurse) =
  case V.proofSuccDistributes (snat @k) (snat @m) of
    E.Refl -> VectorApp app'
  where
    app' :: Closure ('S (Plus k m)) v -> V.Vec ('S m) (Val v) -> f (Closure k v)
    app' cl (a V.:<| as) = recurse (appOne cl a) as

-- app' (Closure env t) (a V.:<| as) = -- recurse (Closure (env :> (Bound, a)) t) as
-- app' (Lift v) (_ V.:<| as) = recurse (Lift v) as
-- app' (LiftClosure cl) (_ V.:<| as) = recurse cl as
-- app' (Function f) (a V.:<| as) = recurse (f a) as

appVector
  :: forall n m f v
   . (Applicative f, SNatI n, SNatI m)
  => Closure (Plus n m) v
  -> V.Vec m (Val v)
  -> f (Closure n v)
appVector = runVectorApp @f @v @n @m (induction appVectorBase appVectorInd)

appVectorFull
  :: forall n f v
   . (Monad f, SNatI n)
  => (Env v -> Term v -> f (Val v))
  -> Closure n v
  -> V.Vec n (Val v)
  -> f (Val v)
appVectorFull eval cl v = do
  cl0 <- appVector @'Z @n cl v
  app eval cl0

appOne :: Closure ('S n) v -> Val v -> Closure n v
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
data VElim v
  = VApp (Val v)
  | VNElim Binder (Closure (A 1) v) (Val v) Binder Binder (Closure (A 2) v)
  | VFst
  | VSnd
  | VQElim Binder (Closure (A 1) v) Binder (Closure (A 1) v) Binder Binder Binder (VProp v)
  | VJ (VTy v) (Val v) Binder Binder (Closure (A 2) v) (Val v) (Val v)
  | VBoxElim
  | VMatch Binder (Closure (A 1) v) [(Name, Binder, Closure (A 1) v)]

showElimHead :: VElim v -> String
showElimHead (VApp {}) = "<application>"
showElimHead (VNElim {}) = "<ℕ-elim>"
showElimHead VFst = "<fst>"
showElimHead VSnd = "<snd>"
showElimHead (VQElim {}) = "<Q-elim>"
showElimHead (VJ {}) = "<J>"
showElimHead VBoxElim = "<▢-elim>"
showElimHead (VMatch {}) = "<match>"

type VSpine v = [VElim v]

data VProp v = VProp (Env v) (Term v)

infixl 8 $$$
($$$) :: (Term v -> Term v) -> VProp v -> VProp v
f $$$ VProp env t = VProp env (f t)

data Val v
  = VRigid Lvl (VSpine v)
  | VFlex MetaVar (Env v) (VSpine v)
  | VU Relevance
  | VLambda Binder (Closure (A 1) v)
  | VPi Relevance Binder (VTy v) (Closure (A 1) v)
  | VZero
  | VSucc (Val v)
  | VNat
  | VExists Binder (VTy v) (Closure (A 1) v)
  | VAbort (VTy v) (VProp v)
  | VEmpty
  | VOne (VProp v)
  | VUnit
  | VEq (Val v) (VTy v) (Val v)
  | VCast (VTy v) (VTy v) (VProp v) (Val v)
  | VPair (Val v) (Val v)
  | VSigma Binder (VTy v) (Closure (A 1) v)
  | VQuotient
      (VTy v)
      Binder
      Binder
      (Closure (A 2) v)
      Binder
      (VProp v)
      Binder
      Binder
      Binder
      (VProp v)
      Binder
      Binder
      Binder
      Binder
      Binder
      (VProp v)
  | VQProj (Val v)
  | VIdRefl (Val v)
  | VIdPath (VProp v)
  | VId (VTy v) (Val v) (Val v)
  | VCons Name (Val v)
  | -- A fixed point will not reduce unless applied to a constructor, so it needs a spine
    VFixedPoint (VTy v) Binder Binder Binder Binder (Closure (A 3) v) (Closure (A 4) v) (Maybe (Val v)) (VSpine v)
  | VMu Binder (VTy v) Binder [(Name, Closure (A 2) v)] (Maybe (Val v))
  | VBoxProof (VProp v)
  | VBox (Val v)

pattern VVar :: Lvl -> Val v
pattern VVar x = VRigid x []

pattern VMeta :: MetaVar -> Env v -> Val v
pattern VMeta mv e = VFlex mv e []

pattern VFun :: Relevance -> VTy v -> VTy v -> VTy v
pattern VFun s a b = VPi s Hole a (Lift b)

pattern VAnd :: VTy v -> VTy v -> VTy v
pattern VAnd a b = VExists Hole a (Lift b)
