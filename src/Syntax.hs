{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Syntax (
  pattern (:>),
  Name,
  Binder (..),
  Loc (..),
  Ix (..),
  Lvl (..),
  Relevance (..),
  ULevel,
  TermF (..),
  Term,
  Type,
  RawF (..),
  Raw,
  pattern R,
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
  pattern Transp,
  pattern Cast,
  pattern CastRefl,
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
  pattern Let,
  pattern Annotation,
  pattern Meta,
  pattern HoleF,
  VElim (..),
  VSpine,
  Val (..),
  pattern VVar,
  pattern VFun,
  pattern VAnd,
  VTy,
  Closure (..),
  ClosureApply (..),
  A,
  Env,
  varMap,
  VarShowable (..),
  prettyPrintTerm,
  prettyPrintTermDebug,
  showElimHead,
  -- eraseSourceLocations
)
where

import Data.Fix
import Error.Diagnose.Position (Position (..))
import GHC.TypeNats qualified as T
import Text.Printf (IsChar (toChar))

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
  deriving (Eq, Ord, Show, Num)

-- Internal de Bruijn levels
newtype Lvl = Lvl Int
  deriving (Eq, Ord, Show, Num)

newtype MetaVar = MetaVar Int
  deriving (Eq, Ord, Show, Num)

-- Universe levels
type ULevel = Int

-- Relevance of a universe.
-- OTT universes may either be proof-relevant, or proof-irrelevant.
data Relevance
  = Relevant
  | Irrelevant
  deriving (Eq)

instance Show Relevance where
  show Relevant = "U"
  show Irrelevant = "Ω"

data TermF proj meta v t
  = VarF v
  | -- Universe terms have a relevance and a level
    UF Relevance
  | LambdaF Binder t
  | AppF t t
  | -- Pi types are annotated with their domain type's relevance and level, and the co-domain level
    PiF Relevance Binder t t
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
  | -- Transport a value along a proof of equality
    TranspF t Binder Binder t t t t
  | -- Type casting
    CastF t t t t
  | CastReflF t t
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

type Term v = Fix (TermF Relevance MetaVar v)

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

pattern Transp :: Term v -> Binder -> Binder -> Term v -> Term v -> Term v -> Term v -> Term v
pattern Transp t x pf b u t' e = Fix (TranspF t x pf b u t' e)

pattern Cast :: Type v -> Type v -> Term v -> Term v -> Term v
pattern Cast a b e t = Fix (CastF a b e t)

pattern CastRefl :: Type v -> Term v -> Term v
pattern CastRefl a t = Fix (CastReflF a t)

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
  , Transp
  , Cast
  , CastRefl
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
  fmap f (TranspF t x pf b u t' e) = TranspF (f t) x pf (f b) (f u) (f t') (f e)
  fmap f (CastF a b e t) = CastF (f a) (f b) (f e) (f t)
  fmap f (CastReflF a t) = CastReflF (f a) (f t)
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
  fmap f (LetF x a t u) = LetF x (f a) (f t) (f u)
  fmap f (AnnotationF t a) = AnnotationF (f t) (f a)
  fmap _ (MetaF m) = MetaF m

instance Functor RawF where
  fmap f (RawF t) = RawF (L {location = location t, syntax = fmap f (syntax t)})

varMap :: forall v v'. (v -> v') -> Term v -> Term v'
varMap f = foldFix alg
  where
    alg :: TermF Relevance MetaVar v (Term v') -> Term v'
    alg (VarF x) = Var (f x)
    alg (UF s) = U s
    alg (LambdaF x e) = Lambda x e
    alg (AppF t u) = App t u
    alg (PiF s x a b) = Pi s x a b
    alg ZeroF = Zero
    alg (SuccF n) = Succ n
    alg (NElimF z a t0 x ih ts n) = NElim z a t0 x ih ts n
    alg NatF = Nat
    alg (PropPairF t u) = PropPair t u
    alg (FstF Irrelevant p) = PropFst p
    alg (SndF Irrelevant p) = PropSnd p
    alg (ExistsF x a b) = Exists x a b
    alg (AbortF a t) = Abort a t
    alg EmptyF = Empty
    alg OneF = One
    alg UnitF = Unit
    alg (EqF t a u) = Eq t a u
    alg (ReflF t) = Refl t
    alg (TranspF t x pf b u t' e) = Transp t x pf b u t' e
    alg (CastF a b e t) = Cast a b e t
    alg (CastReflF a t) = CastRefl a t
    alg (PairF t u) = Pair t u
    alg (FstF Relevant p) = Fst p
    alg (SndF Relevant p) = Snd p
    alg (SigmaF x a b) = Sigma x a b
    alg (QuotientF a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt) =
      Quotient a x y r rx rr sx sy sxy rs tx ty tz txy tyz rt
    alg (QProjF t) = QProj t
    alg (QElimF z b x tpi px py pe p u) = QElim z b x tpi px py pe p u
    alg (IdReflF t) = IdRefl t
    alg (IdPathF t) = IdPath t
    alg (JF a t x pf b u t' e) = J a t x pf b u t' e
    alg (IdF a t u) = Id a t u
    alg (LetF x a t u) = Let x a t u
    alg (AnnotationF t a) = Annotation t a
    alg (MetaF m) = Meta m

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
  showsVar x _ = showString (map toChar x)

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

    showRelevance :: Relevance -> ShowS
    showRelevance Relevant = chr 'U'
    showRelevance Irrelevant = chr 'Ω'

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
    go _ _ (U s) = showRelevance s
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
      let domain = showParen True (binder x . str " :" . showRelevance s . space . go precLet ns a)
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
      par prec precPi (go precApp ns t . str " ~[" . go precAtom ns a . str "] " . go precApp ns u)
    go prec ns (Refl t) = par prec precApp (str "refl " . go precAtom ns t)
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
    go prec ns (CastRefl a t) =
      par prec precApp (str "castrefl" . showParen True (go precLet ns a . comma . go precLet ns t))
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

type Env v = [Val v]

data Arity = Z | S Arity

type family A (n :: T.Nat) :: Arity where
  A 0 = 'Z
  A n = 'S (A (n T.- 1))

data Closure (n :: Arity) v where
  Closure :: forall n v. Env v -> Term v -> Closure n v
  Lift :: forall n v. Val v -> Closure n v
  Function :: (Val v -> Closure n v) -> Closure ('S n) v

class ClosureApply (n :: Arity) cl v | cl -> v where
  app :: (Env v -> Term v -> Val v) -> Closure n v -> cl

instance ClosureApply 'Z (Val v) v where
  app eval (Closure env t) = eval env t
  app _ (Lift v) = v

instance ClosureApply n res v => ClosureApply ('S n) (Val v -> res) v where
  app eval (Closure env t) u = app eval (Closure @n @v (env :> u) t)
  app eval (Lift v) _ = app eval (Lift @n @v v)
  app eval (Function f) u = app eval (f u)

type VTy = Val

-- Note that [~] is an eliminator for the universe, however it does not
-- have a single point on which it might block. Therefore, it cannot be an
-- eliminator in a spine
data VElim v
  = VApp (Val v)
  | VNElim Binder (Closure (A 1) v) (Val v) Binder Binder (Closure (A 2) v)
  | VFst
  | VSnd
  | VQElim Binder (Closure (A 1) v) Binder (Closure (A 1) v)
  | VJ (VTy v) (Val v) Binder Binder (Closure (A 2) v) (Val v) (Val v)

showElimHead :: VElim v -> String
showElimHead (VApp {}) = "<application>"
showElimHead (VNElim {}) = "<ℕ-elim>"
showElimHead (VFst {}) = "<fst>"
showElimHead (VSnd {}) = "<snd>"
showElimHead (VQElim {}) = "<Q-elim>"
showElimHead (VJ {}) = "<J>"

type VSpine v = [VElim v]

data Val v
  = VRigid Lvl (VSpine v)
  | VU Relevance
  | VLambda Binder (Closure (A 1) v)
  | VPi Relevance Binder (VTy v) (Closure (A 1) v)
  | VZero
  | VSucc (Val v)
  | VNat
  | VExists Binder (VTy v) (Closure (A 1) v)
  | VAbort (VTy v)
  | VEmpty
  | VOne
  | VUnit
  | VEq (Val v) (VTy v) (Val v)
  | VCast (VTy v) (VTy v) (Val v)
  | VPair (Val v) (Val v)
  | VSigma Binder (VTy v) (Closure (A 1) v)
  | VQuotient (VTy v) Binder Binder (Closure (A 2) v)
  | VQProj (Val v)
  | VIdRefl (Val v)
  | VIdPath
  | VId (VTy v) (Val v) (Val v)

pattern VVar :: Lvl -> Val v
pattern VVar x = VRigid x []

pattern VFun :: Relevance -> VTy v -> VTy v -> VTy v
pattern VFun s a b = VPi s Hole a (Lift b)

pattern VAnd :: VTy v -> VTy v -> VTy v
pattern VAnd a b = VExists Hole a (Lift b)

-- pattern VFun :: Relevance -> VTy v -> VTy v -> VTy v
-- pattern VFun s a b = VPi s "_" a (Const b)

-- pattern VAnd :: VTy v -> VTy v -> VTy v
-- pattern VAnd a b = VExists "_" a (Const b)
