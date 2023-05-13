{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ViewPatterns #-}

module Experiment.ExampleProofs where

import Error
import Eval
import MonadChecker

import Parser.Parser
import PrettyPrinter

import Syntax
import TypeChecker

import Control.Monad.Except
import Control.Monad.State
import Data.Function ((&))
import Data.Functor.Identity

import Control.Monad.Oops
import Error.Diagnose

import Text.RawString.QQ

boolAsQuotient :: String
boolAsQuotient =
  [r|
    let castrefl : (A :U U) -> (t :U A) -> t ~ cast(A, A, refl A, t) =
      λA. λt. refl t
    in
    let cast_compose : (A :U U) -> (B :U U) -> (C :U U)
                    -> (AB :Ω A ~[U] B) -> (BC :Ω B ~[U] C)
                    -> (x :U A)
                    -> cast(A, C, trans(A, B, C, AB, BC), x) ~[C] cast(B, C, BC, cast(A, B, AB, x)) =
      λA. λB. λC. λAB. λBC. λx.
        transp(B, B' BB'. cast(A, B', trans(A, B, B', AB, BB'), x) ~[B'] cast(B, B', BB', cast(A, B, AB, x)),
               castrefl B (cast(A, B, AB, x)), C, BC)
    in

    let R : ℕ -> ℕ -> Ω =
      λx. λy. rec(_. Ω, rec(_. Ω, ⊤, _ _. ⊥, y), _ _. rec(_. Ω, ⊥, _ _. ⊤, y), x)
    in
    let Rr : (x :U ℕ) -> R x x =
      λx. rec(z. R z z, *, _ _. *, x)
    in
    let Rs : (x :U ℕ) -> (y :U ℕ)
          -> R x y -> R y x =
      λx. λy. rec(y'. R x y' -> R y' x,
                  rec(x'. R x' 0 -> R 0 x', λw. w, _ _. λw. w, x),
                  k _. rec(x'. R x' (S k) -> R (S k) x', λw. w, _ _. λw. w, x),
                  y)
    in
    let Rt : (x :U ℕ) -> (y :U ℕ) -> (z :U ℕ)
          -> R x y -> R y z -> R x z =
      λx. λy. λz. rec(z'. R x y -> R y z' -> R x z',
                      rec(y'. R x y' -> R y' 0 -> R x 0,
                          λx0. λ_. x0,
                          k _. λ_. λw. ⊥-elim(R x 0, w),
                          y),
                      k _. rec(y'. R x y' -> R y' (S k) -> R x (S k),
                               λ_. λw. ⊥-elim(R x (S k), w),
                               l _. rec(x'. R x' (S l) -> R (S l) (S k) -> R x' (S k),
                                        λw. λ_. w,
                                        _ _. λ_. λ_. *,
                                        x),
                               y),
                      z)
    in

    let Bool : U =
      ℕ / (x y. R x y,
           x. Rr x,
           x y xRy. Rs x y xRy,
           x y z xRy yRz. Rt x y z xRy yRz)
    in
    let true : Bool = π 0 in
    let false : Bool = π (S 0) in
    let if : (B :U Bool -> U) -> (c :U Bool) -> B true -> B false -> B c =
      λB. λc. λt. λf.
        let congB : (x :U ℕ) -> (y :U ℕ) -> R x y -> B (π x) ~[U] B (π y) =
          λx. λy. λxRy. ap(U, x. B x, (π x : Bool), π y, xRy)
        in
        let choose : (x :U ℕ) -> B (π x) =
          λx. rec(x'. B (π x'), t, k _. cast(B false, B (π (S k)),
                                             congB (S 0) (S k) *,
                                             f), x)
        in
        let presTRhs : (x :U ℕ) -> (y :U ℕ) -> R x y -> Ω =
          λx. λy. λxRy.
            (choose x) ~[B (π x)] cast(B (π y), B (π x), congB y x (Rs x y xRy), choose y)
        in
        let presT : (x :U ℕ) -> (y :U ℕ) -> Ω =
          λx. λy. (xRy :Ω R x y) -> presTRhs x y xRy
        in
        let pres : (x :U ℕ) -> (y :U ℕ) -> presT x y =
          λx. λy. rec(x'. presT x' y,
                        rec(y'. presT 0 y',
                            λ_. castrefl (B true) t,
                            l _. λw. ⊥-elim(presTRhs 0 (S l) w, w),
                            y),
                      k _.
                        rec(y'. presT (S k) y',
                            λw. ⊥-elim(presTRhs (S k) 0 w, w),
                            l _. λ_. cast_compose (B false) (B (π (S l))) (B (π (S k)))
                                                        (congB (S 0) (S l) *)
                                                        (congB (S l) (S k) *)
                                                        f,
                            y),
                      x)
        in
        Q-elim(z. B z,
               x. choose x,
               x y e. pres x y e,
               c)
    in
    if (λb. if (λ_. U) b ℕ (ℕ × ℕ)) true (S 0) (0; S (S 0))
  |]

stlcNbE :: String
stlcNbE =
  [r|
    let Type : 1 → U =
      μTy : 1 → U. λ_.
        [ 'Unit : 1 → Ty !
        ; 'Product : (Ty ! × Ty !) → Ty !
        ; 'Function : (Ty ! × Ty !) → Ty !
        ]
      functor A B f _ x =
        match x as _ return (lift [Ty] B) ! with
        | 'Unit (_, _) → 'Unit (!, *)
        | 'Product (τ₁-τ₂, _) → 'Product ((f ! (fst τ₁-τ₂); f ! (snd τ₁-τ₂)), *)
        | 'Function (τ₁-τ₂, _) → 'Function ((f ! (fst τ₁-τ₂); f ! (snd τ₁-τ₂)), *)
    in
    let 𝟙 : Type ! = 'Unit (!, *) in
    let _✶_ : Type ! → Type ! → Type ! =
      λt. λu. 'Product ((t; u), *)
    in
    let _⇒_ : Type ! → Type ! → Type ! =
      λdom. λcod. 'Function ((dom; cod), *)
    in
    let 𝔽↓T : 1 → U =
      μCtx : 1 → U. λ_.
        [ 'Empty : 1 → Ctx !
        ; 'Extend : (Ctx ! × Type !) → Ctx !
        ]
      functor A B f _ x =
        match x as _ return (lift [Ctx] B) ! with
        | 'Empty (_, _) → 'Empty (!, *)
        | 'Extend (Γ-τ, _) → 'Extend ((f ! (fst Γ-τ); snd Γ-τ), *)
    in
    let · : 𝔽↓T ! = 'Empty (!, *) in
    let _∷_ : 𝔽↓T ! → Type ! -> 𝔽↓T ! =
      λΓ. λτ. 'Extend ((Γ; τ), *)
    in
    let Ix : (Type ! × 𝔽↓T !) → U =
      μIx : (Type ! × 𝔽↓T !) → U. λτ-Γ.
        [ 'Ix0 : (Γ' : 𝔽↓T !) → Ix (fst τ-Γ; Γ' ∷ (fst τ-Γ))
        ; 'IxS : (τ'-Γ' : Type ! × (Σ(Γ' : 𝔽↓T !). Ix (fst τ-Γ; Γ'))) → Ix (fst τ-Γ; (fst (snd τ'-Γ')) ∷ (fst τ'-Γ'))
        ]
    in
    let 𝔽↓̃τ : (𝔽↓T ! × 𝔽↓T !) → U =
      λCs.
        let Δ : 𝔽↓T ! = fst Cs in
        let Γ : 𝔽↓T ! = snd Cs in
        (τ :U Type !) → Ix (τ; Δ) → Ix (τ; Γ)
    in
    let Term : (Type ! × 𝔽↓T !) → U =
      μTm : (Type ! × 𝔽↓T !) → U. λτ-Γ.
        [ 'Var : (Ix τ-Γ) → Tm τ-Γ
        ; 'One : 1 → Tm (𝟙; snd τ-Γ)
        ; 'Pair : (τ₁-τ₂ : Σ(τ₁ : Type !). Σ(τ₂ : Type !). (Tm (τ₁; snd τ-Γ) × Tm (τ₂; snd τ-Γ))) → Tm ((fst τ₁-τ₂) ✶ (fst (snd τ₁-τ₂)); snd τ-Γ)
        ; 'Fst : (Σ(τ₂ : Type !). Tm (((fst τ-Γ) ✶ τ₂); snd τ-Γ)) → Tm τ-Γ
        ; 'Snd : (Σ(τ₁ : Type !). Tm ((τ₁ ✶ (fst τ-Γ)); snd τ-Γ)) → Tm τ-Γ
        ; 'Lambda : (τ₁-τ₂ : Σ(τ₁ : Type !). Σ(τ₂ : Type !). Tm (τ₂; ((snd τ-Γ) ∷ τ₁))) → Tm ((fst τ₁-τ₂) ⇒ (fst (snd τ₁-τ₂)); snd τ-Γ)
        ; 'App : (Σ(τ₁ : Type !). Tm ((τ₁ ⇒ (fst τ-Γ)); snd τ-Γ) × Tm (τ₁; snd τ-Γ)) → Tm τ-Γ
        ]
    in
    let Form : 1 → U =
      μForm : 1 → U. λ_. ['Ne : 1 → Form !; 'Nf : 1 → Form !]
    in
    let Ne : Form ! = 'Ne (!, *) in
    let Nf : Form ! = 'Nf (!, *) in
    let Normal : (Form ! × (Type ! × 𝔽↓T !)) → U =
      μNormal : (Form ! × (Type ! × 𝔽↓T !)) → U. λf-τ-Γ.
        [ 'VVar : Ix (snd f-τ-Γ) → Normal (Ne; snd f-τ-Γ)
        ; 'VOne : 1 → Normal (Nf; (𝟙; snd (snd f-τ-Γ)))
        ; 'VPair : (τ₁-τ₂ : Σ(τ₁ : Type !). Σ(τ₂ : Type !). (Normal (Nf; (τ₁; snd (snd f-τ-Γ))) × Normal (Nf; (τ₂; snd (snd f-τ-Γ))))) → Normal (Nf; ((fst τ₁-τ₂) ✶ (fst (snd τ₁-τ₂)); snd (snd f-τ-Γ)))
        ; 'VFst : (Σ(τ₂ : Type !). Normal (Ne; ((fst (snd f-τ-Γ)) ✶ τ₂; snd (snd f-τ-Γ)))) → Normal (Ne; snd f-τ-Γ)
        ; 'VSnd : (Σ(τ₁ : Type !). Normal (Ne; (τ₁ ✶ (fst (snd f-τ-Γ)); snd (snd f-τ-Γ)))) → Normal (Ne; snd f-τ-Γ)
        ; 'VLambda : (τ₁-τ₂ : Σ(τ₁ : Type !). Σ(τ₂ : Type !). Normal (Nf; (τ₂; ((snd (snd f-τ-Γ)) ∷ τ₁)))) → Normal (Nf; ((fst τ₁-τ₂) ⇒ (fst (snd τ₁-τ₂)); snd (snd f-τ-Γ)))
        ; 'VApp : (Σ(τ₁ : Type !). Normal (Ne; (τ₁ ⇒ (fst (snd f-τ-Γ)); snd (snd f-τ-Γ))) × Normal (Nf; (τ₁; snd (snd f-τ-Γ)))) → Normal (Ne; snd f-τ-Γ)
        ]
    in
    let ℳ : Type ! → 𝔽↓T ! → U = λτ. λΓ. Normal (Ne; (τ; Γ)) in
    let 𝒩 : Type ! → 𝔽↓T ! → U = λτ. λΓ. Normal (Nf; (τ; Γ)) in
    let pshf : (τ :U Type !) → (Δ :U 𝔽↓T !) → ℳ τ Δ → (Γ :U 𝔽↓T !) → 𝔽↓̃τ (Δ; Γ) → ℳ τ Γ =
      λτ. λΔ.
        (fix [Normal as N] pshf f-τ'-Δ' v :
          let f : Form ! = fst f-τ'-Δ' in
          let τ' : Type ! = fst (snd f-τ'-Δ') in
          let Δ' : 𝔽↓T ! = snd (snd f-τ'-Δ') in
          (Γ :U 𝔽↓T !) → 𝔽↓̃τ (Δ'; Γ) → Normal (f; (τ'; Γ)) =
        let f : Form ! = fst f-τ'-Δ' in
        let τ' : Type ! = fst (snd f-τ'-Δ') in
        let Δ' : 𝔽↓T ! = snd (snd f-τ'-Δ') in
        λΓ. λρ.
          match v as _ return Normal (f; (τ'; Γ)) with
          | 'VVar (ix, pf) → 'VVar (ρ τ' ix, <fst pf, <fst (snd pf), refl Γ>>)
          | 'VOne (_, pf) → 'VOne (!, <fst pf, <fst (snd pf), refl Γ>>)
          | 'VPair (τ₁-τ₂-t-u, pf) →
            let τ₁ : Type ! = fst τ₁-τ₂-t-u in
            let τ₂ : Type ! = fst (snd τ₁-τ₂-t-u) in
            let t : N (Nf; (τ₁; Δ')) = fst (snd (snd τ₁-τ₂-t-u)) in
            let u : N (Nf; (τ₂; Δ')) = snd (snd (snd τ₁-τ₂-t-u)) in
            'VPair ((τ₁; (τ₂; (pshf (Nf; (τ₁; Δ')) t Γ ρ; pshf (Nf; (τ₂; Δ')) u Γ ρ))), <fst pf, <fst (snd pf), refl Γ>>)
          | 'VFst (τ₂-t, pf) →
            let τ₂ : Type ! = fst τ₂-t in
            let t : N (Ne; (τ' ✶ τ₂; Δ')) = snd τ₂-t in
            'VFst ((τ₂; pshf (Ne; (τ' ✶ τ₂; Δ')) t Γ ρ), <fst pf, <fst (snd pf), refl Γ>>)
          | 'VSnd (τ₁-t, pf) →
            let τ₁ : Type ! = fst τ₁-t in
            let t : N (Ne; (τ₁ ✶ τ'; Δ')) = snd τ₁-t in
            'VSnd ((τ₁; pshf (Ne; (τ₁ ✶ τ'; Δ')) t Γ ρ), <fst pf, <fst (snd pf), refl Γ>>)
          | 'VLambda (τ₁-τ₂-t, pf) →
            let τ₁ : Type ! = fst τ₁-τ₂-t in
            let τ₂ : Type ! = fst (snd τ₁-τ₂-t) in
            let t : N (Nf; (τ₂; Δ' ∷ τ₁)) = snd (snd τ₁-τ₂-t) in
            let ρ' : 𝔽↓̃τ (Δ' ∷ τ₁; Γ ∷ τ₁) =
              λτ. λix.
                match ix as _ return Ix (τ; Γ ∷ τ₁) with
                | 'Ix0 (Δ'', pf) → 'Ix0 (Γ, <refl τ, <refl Γ, snd (snd pf)>>)
                | 'IxS (τ'-Δ''-ix, pf) →
                  let τ' : Type ! = fst τ'-Δ''-ix in
                  let Δ'' : 𝔽↓T ! = fst (snd τ'-Δ''-ix) in
                  let ix-Δ''-eq-ix-Δ' : Ix (τ; Δ'') ~ Ix (τ; Δ') =
                    ap(U, Γ'. Ix (τ; Γ'), Δ'', Δ', fst (snd pf))
                  in
                  let ix : Ix (τ; Δ') = cast(Ix (τ; Δ''), Ix (τ; Δ'), ix-Δ''-eq-ix-Δ', snd (snd τ'-Δ''-ix)) in
                  'IxS ((τ'; (Γ; ρ τ ix)), <refl τ, <refl Γ, snd (snd pf)>>)
            in
            'VLambda ((τ₁; (τ₂; pshf (Nf; (τ₂; Δ' ∷ τ₁)) t (Γ ∷ τ₁) ρ')), <fst pf, <fst (snd pf), refl Γ>>)
          | 'VApp (τ₁-t-u, pf) →
            let τ₁ : Type ! = fst τ₁-t-u in
            let t : N (Ne; (τ₁ ⇒ τ'; Δ')) = fst (snd τ₁-t-u) in
            let u : N (Nf; (τ₁; Δ')) = snd (snd τ₁-t-u) in
            'VApp ((τ₁; (pshf (Ne; (τ₁ ⇒ τ'; Δ')) t Γ ρ; pshf (Nf; (τ₁; Δ')) u Γ ρ)), <fst pf, <fst (snd pf), refl Γ>>)
        ) (Ne; (τ; Δ))
    in
    let ⟦_⟧_ : Type ! → 𝔽↓T ! → U =
      (fix [Type as Ty] SemTy _ ty : 𝔽↓T ! → U = λΓ.
        match ty as _ return U with
        | 'Unit (_, _) → 1
        | 'Product (p, _) →
          let τ₁ : Ty ! = fst p in
          let τ₂ : Ty ! = snd p in
          SemTy ! τ₁ Γ × SemTy ! τ₂ Γ
        | 'Function (f, _) →
          let τ₁ : Ty ! = fst f in
          let τ₂ : Ty ! = snd f in
          (Δ :U 𝔽↓T !) → 𝔽↓̃τ (Γ; Δ) → SemTy ! τ₁ Δ → SemTy ! τ₂ Δ) !
    in
    let Π : 𝔽↓T ! → 𝔽↓T ! → U =
      (fix [𝔽↓T as Ctx] Env _ Γ : 𝔽↓T ! → U = λΔ.
        match Γ as _ return U with
        | 'Empty (_, _) → 1
        | 'Extend (Γ-τ, _) →
          let Γ : Ctx ! = fst Γ-τ in
          let τ : Type ! = snd Γ-τ in
          Env ! Γ Δ × ⟦ τ ⟧ Δ) !
    in
    let rn : (Γ :U 𝔽↓T !) → (Δ :U 𝔽↓T !) → 𝔽↓̃τ (Δ; Γ) → (τ :U Type !) → ⟦ τ ⟧ Δ → ⟦ τ ⟧ Γ =
      λΓ. λΔ. λρ.
        (fix [Type as Ty view ι] rn _ τ : ⟦ (ι ! τ) ⟧ Δ → ⟦ (ι ! τ) ⟧ Γ =
          match τ as τ' return
            let τ' : Type ! = in (fmap[Type](Ty, Type, ι, !, τ')) in
            ⟦ τ' ⟧ Δ → ⟦ τ' ⟧ Γ
          with
          | 'Unit (_, _) → λ_. !
          | 'Product (τ₁-τ₂, _) →
            let τ₁ : Ty ! = fst τ₁-τ₂ in
            let τ₂ : Ty ! = snd τ₁-τ₂ in
            λpair.
              let t : ⟦ (ι ! τ₁) ⟧ Δ = fst pair in
              let u : ⟦ (ι ! τ₂) ⟧ Δ = snd pair in
              (rn ! τ₁ (fst pair); rn ! τ₂ (snd pair))
          | 'Function (τ₁-τ₂, _) →
            let τ₁ : Ty ! = fst τ₁-τ₂ in
            let τ₂ : Ty ! = snd τ₁-τ₂ in
            λf. λΔ'. λρ'. f Δ' (λχ. λix. ρ' χ (ρ χ ix))) !
    in
    let Π-eq-Π : (Γ :U 𝔽↓T !) → (Γ' :U 𝔽↓T !) → (Δ :U 𝔽↓T !) → (Γ ~ Γ') → Π Γ Δ ~ Π Γ' Δ =
      λΓ. λΓ'. λΔ. λpf. ap(U, Γ''. Π Γ'' Δ, Γ, Γ', pf)
    in
    let lookup : (τ :U Type !) → (Γ :U 𝔽↓T !) → Ix (τ; Γ) → (Δ :U 𝔽↓T !) → Π Γ Δ → ⟦ τ ⟧ Δ =
      λτ. λΓ.
      (fix [Ix as I] lookup τ-Γ ix : (Δ :U 𝔽↓T !) → Π (snd τ-Γ) Δ → ⟦ (fst τ-Γ) ⟧ Δ =
        let τ : Type ! = fst τ-Γ in
        let Γ : 𝔽↓T ! = snd τ-Γ in
        λΔ. λenv.
          match ix as _ return ⟦ τ ⟧ Δ with
          | 'Ix0 (Γ', pf) →
            let env-cast : Π (Γ' ∷ τ) Δ =
              cast(Π Γ Δ, Π (Γ' ∷ τ) Δ, Π-eq-Π Γ (Γ' ∷ τ) Δ (sym(_, _, snd pf)), env)
            in
            snd env-cast
          | 'IxS (τ'-Γ'-ix, pf) →
            let τ' : Type ! = fst τ'-Γ'-ix in
            let Γ' : 𝔽↓T ! = fst (snd τ'-Γ'-ix) in
            let ix' : I (τ; Γ') = snd (snd τ'-Γ'-ix) in
            let env-cast : Π (Γ' ∷ τ') Δ =
              cast(Π Γ Δ, Π (Γ' ∷ τ') Δ, Π-eq-Π Γ (Γ' ∷ τ') Δ (sym(_, _, snd pf)), env)
            in
            lookup (τ; Γ') ix' Δ (fst env-cast)) (τ; Γ)
    in
    let __⟦_⟧__ : (Γ :U 𝔽↓T !) → (τ :U Type !) → Term (τ; Γ) → (Δ :U 𝔽↓T !) → Π Γ Δ → ⟦ τ ⟧ Δ =
      λΓ. λτ.
      (fix [Term as Tm ] eval τ-Γ tm : (Δ :U 𝔽↓T !) → Π (snd τ-Γ) Δ → ⟦ (fst τ-Γ) ⟧ Δ =
        let τ : Type ! = fst τ-Γ in
        let Γ : 𝔽↓T ! = snd τ-Γ in
        λΔ. λenv.
          match tm as _ return ⟦ τ ⟧ Δ with
          | 'Var (ix, _) → lookup τ Γ ix Δ env
          | 'One (_, pf) → cast(1, ⟦ τ ⟧ Δ, ap(U, τ'. ⟦ τ' ⟧ Δ, 𝟙, τ, fst pf), !)
          | 'Pair (t-u, pf) →
            let τ₁ : Type ! = fst t-u in
            let τ₂ : Type ! = fst (snd t-u) in
            let t : Tm (τ₁; Γ) = fst (snd (snd t-u)) in
            let u : Tm (τ₂; Γ) = snd (snd (snd t-u)) in
            let vt : ⟦ τ₁ ⟧ Δ =
              eval (τ₁; Γ) t Δ env
            in
            let vu : ⟦ τ₂ ⟧ Δ =
              eval (τ₂; Γ) u Δ env
            in
            cast(⟦ τ₁ ⟧ Δ × ⟦ τ₂ ⟧ Δ, ⟦ τ ⟧ Δ, ap(U, τ'. ⟦ τ' ⟧ Δ, τ₁ ✶ τ₂, τ, fst pf), (vt; vu))
          | 'Fst (τ₂-t, _) →
            let τ₂ : Type ! = fst τ₂-t in
            let t : Tm (τ ✶ τ₂; Γ) = snd τ₂-t in
            let vt : ⟦ τ ⟧ Δ × ⟦ τ₂ ⟧ Δ =
              eval (τ ✶ τ₂; Γ) t Δ env
            in
            fst vt
          | 'Snd (τ₁-t, _) →
            let τ₁ : Type ! = fst τ₁-t in
            let t : Tm (τ₁ ✶ τ; Γ) = snd τ₁-t in
            let vt : ⟦ τ₁ ⟧ Δ × ⟦ τ ⟧ Δ =
              eval (τ₁ ✶ τ; Γ) t Δ env
            in
            snd vt
          | 'Lambda (τ₁-τ₂-t, pf) →
            let τ₁ : Type ! = fst τ₁-τ₂-t in
            let τ₂ : Type ! = fst (snd τ₁-τ₂-t) in
            let t : Tm (τ₂; Γ ∷ τ₁) = snd (snd τ₁-τ₂-t) in
            let Λt : (Δ' :U 𝔽↓T !) → 𝔽↓̃τ (Δ; Δ') → ⟦ τ₁ ⟧ Δ' → ⟦ τ₂ ⟧ Δ' =
              λΔ'. λf. λχ.
                let rn-env : (Ξ :U 𝔽↓T !) → Π Ξ Δ → 𝔽↓̃τ (Δ; Δ') → Π Ξ Δ' =
                  (fix [𝔽↓T as Ctx view ι] rn-env _ Ξ : Π (ι ! Ξ) Δ → 𝔽↓̃τ (Δ; Δ') → Π (ι ! Ξ) Δ' =
                    match Ξ as Ξ' return
                      let Ξ'' : 𝔽↓T ! = in (fmap[𝔽↓T](Ctx, 𝔽↓T, ι, !, Ξ')) in
                      Π Ξ'' Δ → 𝔽↓̃τ (Δ; Δ') → Π Ξ'' Δ'
                    with
                    | 'Empty (_, _) → λ_. λ_. !
                    | 'Extend (Ξ'-τ', _) →
                      let Ξ' : Ctx ! = fst Ξ'-τ' in
                      let τ' : Type ! = snd Ξ'-τ' in
                      λε. λρ.
                        let ε'-χ : Π ((ι ! Ξ') ∷ τ') Δ = ε in
                        (rn-env ! Ξ' (fst ε'-χ) ρ; rn Δ' Δ ρ τ' (snd ε'-χ))) !
                in
                eval (τ₂; Γ ∷ τ₁) t Δ' (rn-env Γ env f; χ)
            in
            cast ((Δ' :U 𝔽↓T !) → 𝔽↓̃τ (Δ; Δ') → ⟦ τ₁ ⟧ Δ' → ⟦ τ₂ ⟧ Δ', ⟦ τ ⟧ Δ, ap(U, τ'. ⟦ τ' ⟧ Δ, τ₁ ⇒ τ₂, τ, fst pf), Λt)
          | 'App (τ₁-t-u, _) →
            let τ₁ : Type ! = fst τ₁-t-u in
            let t : Tm (τ₁ ⇒ τ; Γ) = fst (snd τ₁-t-u) in
            let u : Tm (τ₁; Γ) = snd (snd τ₁-t-u) in
            (eval (τ₁ ⇒ τ; Γ) t Δ env) Δ (λ_. λx. x) (eval (τ₁; Γ) u Δ env)) (τ; Γ)
    in
    let q-u : (τ :U Type !) →
          (f :U Form !) → (Γ :U 𝔽↓T !) →
          (match f as _ return U with
          | 'Ne (_, _) → ℳ τ Γ → ⟦ τ ⟧ Γ
          | 'Nf (_, _) → ⟦ τ ⟧ Γ → 𝒩 τ Γ) =
      λτ. (fix [Type as Ty view ι] q-u _ τ :
          (f :U Form !) → (Γ :U 𝔽↓T !) →
          (match f as _ return U with
          | 'Ne (_, _) → ℳ (ι ! τ) Γ → ⟦ (ι ! τ) ⟧ Γ
          | 'Nf (_, _) → ⟦ (ι ! τ) ⟧ Γ → 𝒩 (ι ! τ) Γ) =
        let q : (τ' :U Ty !) → (Γ' :U 𝔽↓T !) → ⟦ (ι ! τ') ⟧ Γ' → 𝒩 (ι ! τ') Γ' =
          λτ'. q-u ! τ' Nf
        in
        let u : (τ' :U Ty !) → (Γ' :U 𝔽↓T !) → ℳ (ι ! τ') Γ' → ⟦ (ι ! τ') ⟧ Γ' =
          λτ'. q-u ! τ' Ne
        in
        λf. λΓ.
          match f as f return
            let τ' : Type ! = in (fmap[Type](Ty, Type, ι, !, τ)) in
            match f as _ return U with
            | 'Ne (_, _) → ℳ τ' Γ → ⟦ τ' ⟧ Γ
            | 'Nf (_, _) → ⟦ τ' ⟧ Γ → 𝒩 τ' Γ
          with
          -- Unquote
          | 'Ne (_, _) →
            (match τ as τ' return
              let τ' : Type ! = in (fmap[Type](Ty, Type, ι, !, τ')) in
              ℳ τ' Γ → ⟦ τ' ⟧ Γ
            with
            | 'Unit (_, _) → λ_. !
            | 'Product (τ₁-τ₂, _) →
              let τ₁ : Ty ! = fst τ₁-τ₂ in
              let τ₂ : Ty ! = snd τ₁-τ₂ in
              λm. (u τ₁ Γ ('VFst ((ι ! τ₂; m), refl ((Ne; (ι ! τ₁; Γ)) : Form ! × (Type ! × 𝔽↓T !))));
                   u τ₂ Γ ('VSnd ((ι ! τ₁; m), refl ((Ne; (ι ! τ₂; Γ)) : Form ! × (Type ! × 𝔽↓T !)))))
            | 'Function (τ₁-τ₂, _) →
              let τ₁ : Ty ! = fst τ₁-τ₂ in
              let τ₂ : Ty ! = snd τ₁-τ₂ in
              let τ₁⇒τ₂ : Type ! = (ι ! τ₁) ⇒ (ι ! τ₂) in
              λm. λΔ. λρ. λχ. u τ₂ Δ ('VApp ((ι ! τ₁; (pshf τ₁⇒τ₂ Γ m Δ ρ; q τ₁ Δ χ)),
                                             refl ((Ne; (ι ! τ₂; Δ)) : Form ! × (Type ! × 𝔽↓T !))))
            )
          -- Quote
          | 'Nf (_, _) →
            (match τ as τ return
              let τ' : Type ! = in (fmap[Type](Ty, Type, ι, !, τ)) in
              ⟦ τ' ⟧ Γ → 𝒩 τ' Γ
            with
            | 'Unit (_, _) → λ_. 'VOne (!, <*, <*, refl Γ>>)
            | 'Product (τ₁-τ₂, _) →
              let τ₁ : Ty ! = fst τ₁-τ₂ in
              let τ₂ : Ty ! = snd τ₁-τ₂ in
              λp.
                let t : ⟦ (ι ! τ₁) ⟧ Γ = fst p in
                let u : ⟦ (ι ! τ₂) ⟧ Γ = snd p in
                'VPair ((ι ! τ₁; (ι ! τ₂; (q τ₁ Γ t; q τ₂ Γ u))), <*, <<refl (ι ! τ₁), refl (ι ! τ₂)>, refl Γ>>)
            | 'Function (τ₁-τ₂, _) →
              let τ₁ : Ty ! = fst τ₁-τ₂ in
              let τ₁' : Type ! = ι ! τ₁ in
              let τ₂ : Ty ! = snd τ₁-τ₂ in
              let τ₂' : Type ! = ι ! τ₂ in
              λf.
                let χ : ⟦ τ₁' ⟧ (Γ ∷ τ₁') =
                  u τ₁ (Γ ∷ τ₁') ('VVar ('Ix0 (Γ, <refl τ₁', <refl Γ, refl τ₁'>>), <*, <refl τ₁', <refl Γ, refl τ₁'>>>))
                in
                let ↑ : 𝔽↓̃τ (Γ; Γ ∷ τ₁') =
                  λτ'. λixΓ. 'IxS ((τ₁'; (Γ; ixΓ)), <refl τ', <refl Γ, refl τ₁'>>)
                in
                'VLambda ((τ₁'; (τ₂'; q τ₂ (Γ ∷ τ₁') (f (Γ ∷ τ₁') ↑ χ))), <*, <<refl τ₁', refl τ₂'>, refl Γ>>)
            )
        ) ! τ
    in
    let q : (τ :U Type !) → (Γ :U 𝔽↓T !) → ⟦ τ ⟧ Γ → 𝒩 τ Γ =
      λτ. q-u τ Nf
    in
    let u : (τ :U Type !) → (Γ :U 𝔽↓T !) → ℳ τ Γ → ⟦ τ ⟧ Γ =
      λτ. q-u τ Ne
    in
    let nbe : (τ :U Type !) → (Γ :U 𝔽↓T !) → Term (τ; Γ) → 𝒩 τ Γ =
      λτ. λΓ. λt.
        let xs : Π Γ Γ =
          (fix [𝔽↓T as Ctx view ι] xs _ Γ : Π (ι ! Γ) (ι ! Γ) =
            match Γ as Γ return
              let Γ' : 𝔽↓T ! = in (fmap[𝔽↓T](Ctx, 𝔽↓T, ι, !, Γ)) in
              Π Γ' Γ'
            with
            | 'Empty (_, _) → !
            | 'Extend (Γ'-τ, _) →
              let Γ' : Ctx ! = fst Γ'-τ in
              let Γ'' : 𝔽↓T ! = ι ! Γ' in
              let τ : Type ! = snd Γ'-τ in
              let χ : ⟦ τ ⟧ (Γ'' ∷ τ) =
                u τ (Γ'' ∷ τ) ('VVar ('Ix0 (Γ'', <refl τ, <refl Γ'', refl τ>>), <*, <refl τ, <refl Γ'', refl τ>>>))
              in
              let shift : (Δ :U 𝔽↓T !) → Π Δ Γ'' → Π Δ (Γ'' ∷ τ) =
                (fix [𝔽↓T as Ctx view ι] shift _ Δ : Π (ι ! Δ) Γ'' → Π (ι ! Δ) (Γ'' ∷ τ) =
                  match Δ as Δ return
                    let Δ' : 𝔽↓T ! = in (fmap[𝔽↓T](Ctx, 𝔽↓T, ι, !, Δ)) in
                    Π Δ' Γ'' → Π Δ' (Γ'' ∷ τ)
                  with
                  | 'Empty (_, _) → λ_. !
                  | 'Extend (Δ'-τ', _) →
                    let Δ' : Ctx ! = fst Δ'-τ' in
                    let τ' : Type ! = snd Δ'-τ' in
                    let ↑ : 𝔽↓̃τ (Γ''; Γ'' ∷ τ) =
                      λτ''. λixΓ''. 'IxS ((τ; (Γ''; ixΓ'')), <refl τ'', <refl Γ'', refl τ>>)
                    in
                    λenv. (shift ! Δ' (fst env); rn (Γ'' ∷ τ) Γ'' ↑ τ' (snd env))
                ) !
              in
              (shift (ι ! Γ') (xs ! Γ'); χ)
            ) ! Γ
        in
        q τ Γ (Γ τ ⟦ t ⟧ Γ xs)
    in
    nbe 𝟙 · ('App ((𝟙; ('Lambda ((𝟙; (𝟙; 'Var ('Ix0 (·, <*, <*, *>>), <*, <*, *>>))), <<*, *>, *>); 'One (!, <*, *>))), <*, *>))
  |]

test :: String -> IO ()
test = testDebug False

testDebug :: Bool -> String -> IO ()
testDebug debug input = do
  (result, mctx) <-
    runStateT
      ( runOopsInEither
          ( result
              & catch @ParseError showReport
              & catch @ConversionError showReport
              & catch @UnificationError showReport
              & catch @CheckError showReport
              & catch @InferenceError showReport
          )
      )
      emptyCheckState
  case result of
    Right (t, tty, knownSort -> Just s) -> do
      putStrLn "Program:"
      putStrLn (prettyPrintTerm [] t)
      putStrLn "\nHas type:"
      putStrLn (prettyPrintTerm [] (runEvaluator (quote 0 tty) (_metaCtx mctx)))
      putStrLn "\nReduces to:"
      putStrLn (prettyPrintTerm [] (runEvaluator (nbe s [] t) (_metaCtx mctx)))
      when debug $ do
        putStrLn "\nMeta context:"
        print mctx
    Right _ -> do
      putStrLn "Program has unsolved sort; cannot be executed."
    Left () ->
      when debug $ do
        putStrLn "\nMeta context:"
        print mctx
  where
    result = do
      let parsed = hoistEither (parse input)
      suspend (mapStateT (pure . runIdentity)) (runChecker (parsed >>= infer emptyContext))
    showReport
      :: CouldBe e ()
      => Reportable r
      => r
      -> ExceptT (Variant e) (StateT CheckState IO) a
    showReport r =
      let diagnostic = addFile def "<test-file>" input
          diagnostic' = addReport diagnostic (report r)
       in do
            lift (printDiagnostic stdout True True 4 defaultStyle diagnostic')
            throw ()

    knownSort :: Relevance -> Maybe Sort
    knownSort Relevant = Just Relevant
    knownSort Irrelevant = Just Irrelevant
    knownSort _ = Nothing
