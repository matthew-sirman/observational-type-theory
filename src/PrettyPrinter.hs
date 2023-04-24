{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module PrettyPrinter (
  VarShowable (..),
  prettyPrintTerm,
  prettyPrintTermDebug,
)
where

import Syntax

import Text.Printf (IsChar (toChar))

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
    go prec ns (Cons c t e) =
      par prec precApp (str c . space . showParen True (go precLet ns t . comma . go precLet ns e))
    go prec ns (In t) =
      par prec precApp (str "in " . go precAtom ns t)
    go prec ns (Out t) =
      par prec precApp (str "out " . go precAtom ns t)
    go prec ns (FLift f a) =
      par prec precApp (str "lift [" . go precLet ns f . str "] " . go precAtom ns a)
    go prec ns (Fmap f a b g p x) =
      let a' = go precLet ns a
          b' = go precLet ns b
          g' = go precLet ns g
          p' = go precLet ns p
          x' = go precLet ns x
          args = showParen True (sep comma [a', b', g', p', x'])
       in par prec precApp (str "fmap [" . go precLet ns f . str "]" . args)
    go prec ns (Match t x p bs) =
      let t' = go precLet ns t
          p' = go precLet (ns :> x) p
          bs' = foldr ((.) . (str "\n" .) . branch) id bs
       in par prec precLet (str "match " . t' . str " as " . binder x . str " return " . p' . str " with" . bs')
      where
        branch :: (Name, Binder, Binder, Term v) -> ShowS
        branch (cons, x, e, t) =
          let cons' = str cons . str " " . showParen True (binder x . comma . binder e)
           in str "| " . cons' . str " -> " . go precLet (ns :> x :> e) t
    go prec ns (FixedPoint i g v f p x c t) =
      let i' = go precLet ns i . showAsAlias g . showViewAlias v
          args = sep space (fmap binder [f, p, x])
          c' = go precLet (ns :> g :> v :> p :> x) c
          t' = go precLet (ns :> g :> v :> f :> p :> x) t
       in par prec precLet (str "fix [" . i' . str "] " . args . str " : " . c' . str " = " . t')
      where
        showAsAlias, showViewAlias :: Binder -> ShowS
        showAsAlias Hole = id
        showAsAlias g = str " as " . binder g
        showViewAlias Hole = id
        showViewAlias v = str " view " . binder v
    go prec ns (Mu _ f t x cs functor) =
      let x' = str "λ" . binder x
          cs' = chr '[' . sep (str "; ") (fmap showCons cs) . chr ']'
       in par prec precLet (str "μ" . str f . str " : " . go precLet ns t . dot . x' . dot . cs' . showFunctor functor)
      where
        showCons :: (Name, Relevance, Binder, Type v, Name, Type v) -> ShowS
        showCons (ci, _, Hole, bi, gi, ixi) =
          let bi' = go precApp (ns :> Name f :> x) bi
              ixi' = go precAtom (ns :> Name f :> x :> Hole) ixi
           in str ci . str " : " . bi' . str " → " . str gi . space . ixi'
        showCons (ci, si, xi, bi, gi, ixi) =
          let bi' = showParen True (binder xi . str " :" . shows si . space . go precLet (ns :> Name f :> x) bi)
              ixi' = go precAtom (ns :> Name f :> x :> xi) ixi
           in str ci . str " : " . bi' . str " → " . str gi . space . ixi'
        showFunctor :: Maybe (FunctorInstance v) -> ShowS
        showFunctor Nothing = id
        showFunctor (Just (FunctorInstanceF a b g p x t)) =
          let args = sep space [binder a, binder b, binder g, binder p, binder x]
              t' = go precLet (ns :> Name f :> a :> b :> g :> p :> x) t
           in str "\n  functor " . args . str " = " . t'
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
