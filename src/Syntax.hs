{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Syntax
  ( Name,
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
    pattern Pair,
    pattern Fst,
    pattern Snd,
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
    pattern Let,
    Val (..),
    VTy,
    vFun,
    vAnd,
    Closure1,
    Closure2,
    Env,
    varMap,
    VarShowable (..),
    prettyPrintTerm,
    prettyPrintTermDebug,
    eraseSourceLocations
  )
where

import Data.Fix
import Text.Printf (IsChar (toChar))
import Error.Diagnose.Position (Position(..))

-- Language source identifiers
type Name = String

-- Syntactic element tagged with a source code location
data Loc a = L
  { location :: Position,
    syntax :: a
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

-- Universe levels
type ULevel = Int

-- Relevance of a universe.
-- OTT universes may either be proof-relevant, or proof-irrelevant.
data Relevance
  = Relevant
  | Irrelevant
  deriving Eq

instance Show Relevance where
  show Relevant = "U"
  show Irrelevant = "Ω"

data TermF v t
  = VarF v
  | -- Universe terms have a relevance and a level
    UF Relevance
  | LambdaF Name t
  | AppF t t
  | -- Pi types are annotated with their domain type's relevance and level, and the co-domain level
    PiF Relevance Name t t
  | ZeroF
  | SuccF t
  | NElimF Name t t Name Name t t
  | NatF
  | PairF t t
  | FstF t
  | SndF t
  | -- Existential types are annotated with their domain and co-domain levels
    ExistsF Name t t
  | AbortF t t
  | EmptyF
  | OneF
  | UnitF
  | -- Observational equality type t ~A u
    EqF t t t
  | ReflF t
  | -- Transport a value along a proof of equality
    TranspF t Name Name t t t t
  | -- Type casting
    CastF t t t t
  | CastReflF t t
  | LetF Name t t t

newtype RawF t = RawF (Loc (TermF Name t))

type Raw = Fix RawF

pattern R :: Position -> TermF Name Raw -> Raw
pattern R sl term = Fix (RawF (L sl term))

{-# COMPLETE R #-}

type Term v = Fix (TermF v)

type Type v = Fix (TermF v)

pattern Var :: v -> Term v
pattern Var x = Fix (VarF x)

pattern U :: Relevance -> Term v
pattern U s = Fix (UF s)

pattern Lambda :: Name -> Term v -> Term v
pattern Lambda x e = Fix (LambdaF x e)

pattern App :: Term v -> Term v -> Term v
pattern App t u = Fix (AppF t u)

pattern Pi :: Relevance -> Name -> Type v -> Type v -> Type v
pattern Pi s x a b = Fix (PiF s x a b)

pattern Zero :: Term v
pattern Zero = Fix ZeroF

pattern Succ :: Term v -> Term v
pattern Succ n = Fix (SuccF n)

pattern NElim :: Name -> Term v -> Term v -> Name -> Name -> Term v -> Term v -> Term v
pattern NElim z p t0 x ih ts n = Fix (NElimF z p t0 x ih ts n)

pattern Nat :: Term v
pattern Nat = Fix NatF

pattern Pair :: Term v -> Term v -> Term v
pattern Pair t u = Fix (PairF t u)

pattern Fst :: Term v -> Term v
pattern Fst p = Fix (FstF p)

pattern Snd :: Term v -> Term v
pattern Snd p = Fix (SndF p)

pattern Exists :: Name -> Term v -> Term v -> Term v
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

pattern Transp :: Term v -> Name -> Name -> Term v -> Term v -> Term v -> Term v -> Term v
pattern Transp t x pf b u t' e = Fix (TranspF t x pf b u t' e)

pattern Cast :: Type v -> Type v -> Term v -> Term v -> Term v
pattern Cast a b e t = Fix (CastF a b e t)

pattern CastRefl :: Type v -> Term v -> Term v
pattern CastRefl a t = Fix (CastReflF a t)

pattern Let :: Name -> Type v -> Term v -> Term v -> Term v
pattern Let x a t u = Fix (LetF x a t u)

{-# COMPLETE
  Var,
  U,
  Lambda,
  App,
  Pi,
  Zero,
  Succ,
  NElim,
  Nat,
  Pair,
  Fst,
  Snd,
  Exists,
  Abort,
  Empty,
  One,
  Unit,
  Eq,
  Refl,
  Transp,
  Cast,
  CastRefl,
  Let
  #-}

instance Functor (TermF v) where
  fmap _ (VarF x) = VarF x
  fmap _ (UF s) = UF s
  fmap f (LambdaF x e) = LambdaF x (f e)
  fmap f (AppF t u) = AppF (f t) (f u)
  fmap f (PiF s x a b) = PiF s x (f a) (f b)
  fmap _ ZeroF = ZeroF
  fmap f (SuccF n) = SuccF (f n)
  fmap f (NElimF z p t0 x ih ts n) = NElimF z (f p) (f t0) x ih (f ts) (f n)
  fmap _ NatF = NatF
  fmap f (PairF t u) = PairF (f t) (f u)
  fmap f (FstF p) = FstF (f p)
  fmap f (SndF p) = SndF (f p)
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
  fmap f (LetF x a t u) = LetF x (f a) (f t) (f u)

instance Functor RawF where
  fmap f (RawF t) = RawF (L { location = location t, syntax = fmap f (syntax t)})

varMap :: forall v v'. (v -> v') -> Term v -> Term v'
varMap f = foldFix alg
  where
    alg :: TermF v (Term v') -> Term v'
    alg (VarF x) = Var (f x)
    alg (UF s) = U s
    alg (LambdaF x e) = Lambda x e
    alg (AppF t u) = App t u
    alg (PiF s x a b) = Pi s x a b
    alg ZeroF = Zero
    alg (SuccF n) = Succ n
    alg (NElimF z p t0 x ih ts n) = NElim z p t0 x ih ts n
    alg NatF = Nat
    alg (PairF t u) = Pair t u
    alg (FstF p) = Fst p
    alg (SndF p) = Snd p
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
    alg (LetF x a t u) = Let x a t u

precAtom, precApp, precPi, precLet :: Int
precAtom = 3
precApp = 2
precPi = 1
precLet = 0

class VarShowable v where
  showsVar :: v -> [Name] -> ShowS

instance VarShowable Ix where
  showsVar (Ix x) ns = shows x -- showString (ns !! x)

instance IsChar s => VarShowable [s] where
  showsVar x _ = showString (map toChar x)

prettyPrintTerm :: VarShowable v => [Name] -> Term v -> String
prettyPrintTerm = prettyPrintTermDebug False

prettyPrintTermDebug :: forall v. VarShowable v => Bool -> [Name] -> Term v -> String
prettyPrintTermDebug debug names tm = go 0 names tm []
  where
    par :: Int -> Int -> ShowS -> ShowS
    par p p' = showParen (p' < p || debug)

    showRelevance :: Relevance -> ShowS
    showRelevance Relevant = ('U' :)
    showRelevance Irrelevant = ('Ω' :)

    comma :: ShowS
    comma = showString ", "

    commaSep :: [ShowS] -> ShowS
    commaSep [] = id
    commaSep [x] = x
    commaSep (x : xs) = x . comma . commaSep xs

    tag :: String -> ShowS
    tag t
      | debug = ('{' :) . showString t . ('}' :)
      | otherwise = id

    go :: Int -> [Name] -> Term v -> ShowS
    go _ ns (Var x) = tag "V" . showsVar x ns
    go _ _ (U s) = showRelevance s
    go prec ns (Lambda x e) =
      let domain = ('λ' :) . showString x
       in par prec precLet (domain . showString ". " . go precLet (x : ns) e)
    go prec ns (App t u) =
      tag "A" . par prec precApp (go precApp ns t . (' ' :) . go precAtom ns u)
    go prec ns (Pi _ "_" a b) =
      let domain = go precApp ns a
          codomain = go precPi ("_" : ns) b
       in tag "Π" . par prec precPi (domain . showString " → " . codomain)
    go prec ns (Pi s x a b) =
      let domain = showParen True (showString x . showString " :" . showRelevance s . (' ' :) . go precLet ns a)
          codomain = go precPi (x : ns) b
       in tag "Π" . par prec precPi (domain . showString " → " . codomain)
    go _ _ Zero = ('Z' :)
    go prec ns (Succ n) = par prec precApp (showString "S " . go precAtom ns n)
    go prec ns (NElim z p t0 x ih ts n) =
      let p' = showString z . showString ". " . go precLet (z : ns) p
          t0' = go precLet ns t0
          ts' = showString x . showString " " . showString ih . showString ". " . go precLet (ih : x : ns) ts
          n' = go precLet ns n
       in par prec precApp (showString "ℕ-elim" . showParen True (commaSep [p', t0', ts', n']))
    go _ _ Nat = ('ℕ' :)
    go _ ns (Pair t u) = ('⟨' :) . go precLet ns t . comma . go precLet ns u . ('⟩' :)
    go prec ns (Fst p) = par prec precApp (showString "fst " . go precAtom ns p)
    go prec ns (Snd p) = par prec precApp (showString "snd " . go precAtom ns p)
    go prec ns (Exists "_" a b) =
      let domain = go precApp ns a
          codomain = go precApp ("_" : ns) b
       in tag "∃" . par prec precPi (domain . showString " ∧ " . codomain)
    go prec ns (Exists x a b) =
      let domain = showParen True (showString x . showString " : " . go precLet ns a)
          codomain = go precPi (x : ns) b
       in par prec precPi (('∃' :) . domain . showString ". " . codomain)
    go prec ns (Abort a t) =
      let a' = go precLet ns a
          t' = go precLet ns t
       in par prec precApp (showString "⊥-elim" . showParen True (a' . comma . t'))
    go _ _ Empty = ('⊥' :)
    go _ _ One = ('*' :)
    go _ _ Unit = ('⊤' :)
    go prec ns (Eq t a u) =
      par prec precPi (go precPi ns t . showString " ~" . go precAtom ns a . (' ' :) . go precPi ns u)
    go prec ns (Refl t) = par prec precApp (showString "refl " . go precAtom ns t)
    go prec ns (Transp t x pf b u v e) =
      let t' = go precLet ns t
          b' = showString x . showString " " . showString pf . showString ". " . go precLet (pf : x : ns) b
          u' = go precLet ns u
          v' = go precLet ns v
          e' = go precLet ns e
       in par prec precApp (showString "transp" . showParen True (commaSep [t', b', u', v', e']))
    go prec ns (Cast a b e t) =
      let a' = go precLet ns a
          b' = go precLet ns b
          e' = go precLet ns e
          t' = go precLet ns t
       in par prec precApp (showString "cast" . showParen True (commaSep [a', b', e', t']))
    go prec ns (CastRefl a t) =
      par prec precApp (showString "castrefl" . showParen True (go precLet ns a . comma . go precLet ns t))
    go prec ns (Let x a t u) =
      let a' = go precLet ns a
          t' = go precLet ns t
          u' = go precLet (x : ns) u
       in par
            prec
            precLet
            ( showString "let " . showString x . showString " : " . a'
                . showString " =\n    "
                . t'
                . showString "\nin\n"
                . u'
            )

eraseSourceLocations :: Raw -> Term Name
eraseSourceLocations = foldFix alg
  where
    alg :: RawF (Term Name) -> Term Name
    alg (RawF l) = Fix (syntax l)

type Env v = [Val v]

-- data Closure v
--   = Closure (Term v) (Env v)
--   | Const (Val v)

-- TODO: Defunctionalise closures
type Closure1 v = Val v -> Val v
type Closure2 v = Val v -> Val v -> Val v

type VTy = Val

data Val v
  = VVar Lvl
  | VU Relevance
  | VLambda Name (Closure1 v)
  | VApp (Val v) (Val v)
  | VPi Relevance Name (VTy v) (Closure1 v)
  | VZero
  | VSucc (Val v)
  | VNElim Name (Closure1 v) (Val v) Name Name (Closure2 v) (Val v)
  | VNat
  | VPair (Term v) (Term v)
  | VFst (Term v)
  | VSnd (Term v)
  | VExists Name (VTy v) (Closure1 v)
  | VAbort (VTy v) (Term v)
  | VEmpty
  | VOne
  | VUnit
  | VEq (Val v) (VTy v) (Val v)
  | VRefl (Term v)
  | VTransp (Term v) Name Name (Term v) (Term v) (Term v) (Term v)
  | VCast (VTy v) (VTy v) (Term v) (Val v)
  | VCastRefl (VTy v) (Term v)

vFun :: Relevance -> VTy v -> VTy v -> VTy v
vFun s a b = VPi s "_" a (const b)

vAnd :: VTy v -> VTy v -> VTy v
vAnd a b = VExists "_" a (const b)

-- pattern VFun :: Relevance -> VTy v -> VTy v -> VTy v
-- pattern VFun s a b = VPi s "_" a (Const b)

-- pattern VAnd :: VTy v -> VTy v -> VTy v
-- pattern VAnd a b = VExists "_" a (Const b)
