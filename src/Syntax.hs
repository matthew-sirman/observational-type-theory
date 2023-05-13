{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Syntax (
  pattern (:>),
  Name,
  Binder (..),
  Loc (..),
  Ix (..),
  Lvl (..),
  lvl2ix,
  MetaVar (..),
  Tag (..),
  RelevanceF (..),
  Relevance,
  Sort,
  pattern SortHole,
  ULevel,
  TermF (..),
  FunctorInstanceF (..),
  FunctorInstanceUniformF (..),
  Term,
  Type,
  FunctorInstance,
  FunctorInstanceUniform,
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
  pattern In,
  pattern FLift,
  pattern FmapAny,
  pattern Fmap,
  pattern FmapUniform,
  pattern MatchAny,
  pattern Match,
  pattern MatchUniform,
  pattern FixedPointAny,
  pattern FixedPoint,
  pattern FixedPointUniform,
  pattern Mu,
  pattern MuUniform,
  pattern Let,
  pattern Annotation,
  pattern Meta,
)
where

import Data.Fix hiding (Mu)

-- import Data.Type.Equality qualified as E
import Data.Void
import Error.Diagnose.Position (Position (..))

-- Snoc lists
infixl 4 :>
pattern (:>) :: [a] -> a -> [a]
pattern xs :> x = x : xs

{-# COMPLETE (:>), [] #-}

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

-- Tag for inductive types
-- This is a hack to get observational equality between
-- literally equivalent inductive types (applied to different arguments),
-- as opposed to structural equality between them.
newtype Tag = Tag Int
  deriving (Eq, Ord, Num)

-- Universe levels
type ULevel = Int

-- Relevance of a universe.
-- OTT universes may either be proof-relevant, or proof-irrelevant.
data RelevanceF meta
  = Relevant
  | Irrelevant
  | SortMeta meta
  deriving (Eq)

type Sort = RelevanceF Void

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

data TermF sort meta tag v t
  = VarF v
  | -- Universe terms have a relevance and a level
    UF (RelevanceF meta)
  | LambdaF Binder t
  | AppF sort t t
  | -- Pi types are annotated with their domain type's relevance and level, and the co-domain level
    PiF (RelevanceF meta) Binder t t
  | ZeroF
  | SuccF t
  | NElimF Binder t t Binder Binder t t
  | NatF
  | PropPairF t t
  | FstF sort t
  | SndF sort t
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
  | ConsF Name t t
  | InF t
  | FLiftF t t
  | FmapF t t t t (Maybe t) t
  | MatchF t Binder t [(Name, Binder, Maybe Binder, t)]
  | FixedPointF t Binder Binder Binder (Maybe Binder) Binder t t
  | MuF tag Name t Binder [(Name, RelevanceF meta, Binder, t, Name, t)] (Maybe (FunctorInstanceF t))
  | MuUniformF tag Name [(Name, t, Name)] (Maybe (FunctorInstanceUniformF t))
  | -- Annotations
    LetF Binder t t t
  | AnnotationF t t
  | MetaF meta

data FunctorInstanceF t = FunctorInstanceF Binder Binder Binder Binder Binder t

data FunctorInstanceUniformF t = FunctorInstanceUniformF Binder Binder Binder Binder t

newtype RawF t = RawF (Loc (TermF () () () Name t))

type Raw = Fix RawF

pattern R :: Position -> TermF () () () Name Raw -> Raw
pattern R sl term = Fix (RawF (L sl term))

pattern HoleF :: TermF () () () Name t
pattern HoleF = MetaF ()

{-# COMPLETE R #-}

type Term v = Fix (TermF Sort MetaVar Tag v)

type Type v = Term v

type FunctorInstance v = FunctorInstanceF (Term v)

type FunctorInstanceUniform v = FunctorInstanceUniformF (Term v)

pattern Var :: v -> Term v
pattern Var x = Fix (VarF x)

pattern U :: Relevance -> Term v
pattern U s = Fix (UF s)

pattern Lambda :: Binder -> Term v -> Term v
pattern Lambda x e = Fix (LambdaF x e)

pattern App :: Sort -> Term v -> Term v -> Term v
pattern App s t u = Fix (AppF s t u)

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

pattern Cons :: Name -> Term v -> Term v -> Term v
pattern Cons c t e = Fix (ConsF c t e)

pattern In :: Term v -> Term v
pattern In t = Fix (InF t)

pattern FLift :: Type v -> Type v -> Term v
pattern FLift f a = Fix (FLiftF f a)

pattern FmapAny :: Type v -> Type v -> Type v -> Term v -> Maybe (Term v) -> Term v -> Term v
pattern FmapAny f a b g p x = Fix (FmapF f a b g p x)

pattern Fmap :: Type v -> Type v -> Type v -> Term v -> Term v -> Term v -> Term v
pattern Fmap f a b g p x = Fix (FmapF f a b g (Just p) x)

pattern FmapUniform :: Type v -> Type v -> Type v -> Term v -> Term v -> Term v
pattern FmapUniform f a b g x = Fix (FmapF f a b g Nothing x)

pattern MatchAny :: Term v -> Binder -> Type v -> [(Name, Binder, Maybe Binder, Term v)] -> Term v
pattern MatchAny t x p bs = Fix (MatchF t x p bs)

sequenceConstructor :: (Name, Binder, Maybe Binder, Term v) -> Maybe (Name, Binder, Binder, Term v)
sequenceConstructor (c, x, Just e, t) = Just (c, x, e, t)
sequenceConstructor (_, _, Nothing, _) = Nothing

pattern Match :: Term v -> Binder -> Type v -> [(Name, Binder, Binder, Term v)] -> Term v
pattern Match t x p bs <- Fix (MatchF t x p (traverse sequenceConstructor -> Just bs))
  where
    Match t x p bs = Fix (MatchF t x p (map (\(c, x, e, t) -> (c, x, Just e, t)) bs))

ignoreParameter :: (Name, Binder, Maybe Binder, Term v) -> Maybe (Name, Binder, Term v)
ignoreParameter (c, x, Nothing, t) = Just (c, x, t)
ignoreParameter (_, _, Just _, _) = Nothing

pattern MatchUniform :: Term v -> Binder -> Type v -> [(Name, Binder, Term v)] -> Term v
pattern MatchUniform t x p bs <- Fix (MatchF t x p (traverse ignoreParameter -> Just bs))
  where
    MatchUniform t x p bs = Fix (MatchF t x p (map (\(c, x, t) -> (c, x, Nothing, t)) bs))

pattern FixedPointAny :: Type v -> Binder -> Binder -> Binder -> Maybe Binder -> Binder -> Type v -> Term v -> Term v
pattern FixedPointAny i g v f p x c t = Fix (FixedPointF i g v f p x c t)

pattern FixedPoint :: Type v -> Binder -> Binder -> Binder -> Binder -> Binder -> Type v -> Term v -> Term v
pattern FixedPoint i g v f p x c t = Fix (FixedPointF i g v f (Just p) x c t)

pattern FixedPointUniform :: Type v -> Binder -> Binder -> Binder -> Binder -> Type v -> Term v -> Term v
pattern FixedPointUniform i g v f x c t = Fix (FixedPointF i g v f Nothing x c t)

pattern Mu :: Tag -> Name -> Type v -> Binder -> [(Name, Relevance, Binder, Type v, Name, Term v)] -> Maybe (FunctorInstance v) -> Type v
pattern Mu tag f t x cs functor = Fix (MuF tag f t x cs functor)

pattern MuUniform :: Tag -> Name -> [(Name, Type v, Name)] -> Maybe (FunctorInstanceUniform v) -> Type v
pattern MuUniform tag f cs functor = Fix (MuUniformF tag f cs functor)

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
  , In
  , FLift
  , Fmap
  , FmapUniform
  , Match
  , MatchUniform
  , FixedPoint
  , FixedPointUniform
  , Mu
  , MuUniform
  , Let
  , Annotation
  , Meta
  #-}

instance Functor FunctorInstanceF where
  fmap f (FunctorInstanceF a b f' p x t) = FunctorInstanceF a b f' p x (f t)

instance Functor FunctorInstanceUniformF where
  fmap f (FunctorInstanceUniformF a b f' x t) = FunctorInstanceUniformF a b f' x (f t)

instance Functor (TermF p m t v) where
  fmap _ (VarF x) = VarF x
  fmap _ (UF s) = UF s
  fmap f (LambdaF x e) = LambdaF x (f e)
  fmap f (AppF s t u) = AppF s (f t) (f u)
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
  fmap f (ConsF c t e) = ConsF c (f t) (f e)
  fmap f (InF t) = InF (f t)
  fmap f (FLiftF f' a) = FLiftF (f f') (f a)
  fmap f (FmapF f' a b g p x) = FmapF (f f') (f a) (f b) (f g) (fmap f p) (f x)
  fmap f (MatchF t x p bs) = MatchF (f t) x (f p) (fmap (fmap f) bs)
  fmap f (FixedPointF i g v f' p x c t) = FixedPointF (f i) g v f' p x (f c) (f t)
  fmap f (MuF tag g t x cs functor) = MuF tag g (f t) x (fmap (\(ci, si, xi, ti, gi, ixi) -> (ci, si, xi, f ti, gi, f ixi)) cs) (fmap (fmap f) functor)
  fmap f (MuUniformF tag g cs functor) = MuUniformF tag g (fmap (\(ci, ti, gi) -> (ci, f ti, gi)) cs) (fmap (fmap f) functor)
  fmap f (LetF x a t u) = LetF x (f a) (f t) (f u)
  fmap f (AnnotationF t a) = AnnotationF (f t) (f a)
  fmap _ (MetaF m) = MetaF m

instance Foldable FunctorInstanceF where
  foldr f e (FunctorInstanceF _ _ _ _ _ t) = f t e

instance Foldable FunctorInstanceUniformF where
  foldr f e (FunctorInstanceUniformF _ _ _ _ t) = f t e

instance Foldable (TermF p m t v) where
  foldr _ e (VarF _) = e
  foldr _ e (UF _) = e
  foldr f e (LambdaF _ t) = f t e
  foldr f e (AppF _ t u) = (f t . f u) e
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
  foldr f e (ConsF _ t p) = (f t . f p) e
  foldr f e (InF t) = f t e
  foldr f e (FLiftF f' a) = (f f' . f a) e
  foldr f e (FmapF f' a b g p x) = (f f' . f a . f b . f g . flip (foldr f) p . f x) e
  foldr f e (MatchF t _ p bs) = (f t . f p) (foldr (\(_, _, _, b) e -> f b e) e bs)
  foldr f e (FixedPointF i _ _ _ _ _ c t) = (f i . f c . f t) e
  foldr f e (MuF _ _ t _ cs functor) = f t (foldr (\(_, _, _, bi, _, ixi) e -> (f bi . f ixi) e) (foldr (flip (foldr f)) e functor) cs)
  foldr f e (MuUniformF _ _ cs functor) = foldr (\(_, bi, _) e -> f bi e) (foldr (flip (foldr f)) e functor) cs
  foldr f e (LetF _ a t u) = (f a . f t . f u) e
  foldr f e (AnnotationF t a) = (f t . f a) e
  foldr _ e (MetaF _) = e

instance Traversable FunctorInstanceF where
  traverse f (FunctorInstanceF a b f' p x t) = FunctorInstanceF a b f' p x <$> f t

instance Traversable FunctorInstanceUniformF where
  traverse f (FunctorInstanceUniformF a b f' x t) = FunctorInstanceUniformF a b f' x <$> f t

instance Traversable (TermF p m t v) where
  traverse _ (VarF x) = pure (VarF x)
  traverse _ (UF s) = pure (UF s)
  traverse f (LambdaF x e) = LambdaF x <$> f e
  traverse f (AppF s t u) = AppF s <$> f t <*> f u
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
  traverse f (ConsF c t e) = ConsF c <$> f t <*> f e
  traverse f (InF t) = InF <$> f t
  traverse f (FLiftF f' a) = FLiftF <$> f f' <*> f a
  traverse f (FmapF f' a b g p x) = FmapF <$> f f' <*> f a <*> f b <*> f g <*> traverse f p <*> f x
  traverse f (MatchF t x p bs) = MatchF <$> f t <*> pure x <*> f p <*> traverse (\(c, x, e, t) -> (c,x,e,) <$> f t) bs
  traverse f (FixedPointF i g v f' p x c t) = FixedPointF <$> f i <*> pure g <*> pure v <*> pure f' <*> pure p <*> pure x <*> f c <*> f t
  traverse f (MuF tag g t x cs functor) =
    MuF tag g <$> f t <*> pure x <*> traverse (\(ci, si, xi, bi, gi, ixi) -> (ci,si,xi,,gi,) <$> f bi <*> f ixi) cs <*> traverse (traverse f) functor
  traverse f (MuUniformF tag g cs functor) =
    MuUniformF tag g <$> traverse (\(ci, bi, gi) -> (ci,,gi) <$> f bi) cs <*> traverse (traverse f) functor
  traverse f (LetF x a t u) = LetF x <$> f a <*> f t <*> f u
  traverse f (AnnotationF t a) = AnnotationF <$> f t <*> f a
  traverse _ (MetaF m) = pure (MetaF m)

instance Functor RawF where
  fmap f (RawF t) = RawF (L {location = location t, syntax = fmap f (syntax t)})
