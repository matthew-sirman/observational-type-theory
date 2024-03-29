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
    let cast_compose : (A :U U) → (B :U U) → (C :U U)
                    → (AB :Ω A ~ B) → (BC :Ω B ~ C)
                    → (x :U A)
                    → cast(A, C, AB ∘ BC, x) ~ cast(B, C, BC, cast(A, B, AB, x)) =
      λA. λB. λC. λAB. λBC. λx.
        transp(B,
               B' BB'.
                 cast(A, B', AB ∘ BB', x) ~ cast(B, B', BB', cast(A, B, AB, x)),
               refl (cast(A, B, AB, x)), C, BC)
    in
    let R : ℕ → ℕ → Ω =
      λx. λy. rec(_. Ω, rec(_. Ω, ⊤, _ _. ⊥, y), _ _. rec(_. Ω, ⊥, _ _. ⊤, y), x)
    in
    let Rr : (x :U ℕ) → R x x =
      λx. rec(z. R z z, *, _ _. *, x)
    in
    let Rs : (x :U ℕ) → (y :U ℕ) → R x y → R y x =
      λx. λy. rec(y'. R x y' → R y' x,
                  rec(x'. R x' 0 → R 0 x', λw. w, _ _. λw. w, x),
                  k _. rec(x'. R x' (S k) → R (S k) x', λw. w, _ _. λw. w, x),
                  y)
    in
    let Rt : (x :U ℕ) → (y :U ℕ) → (z :U ℕ) → R x y → R y z → R x z =
      λx. λy. λz. rec(z'. R x y → R y z' → R x z',
                      rec(y'. R x y' → R y' 0 → R x 0,
                          λx0. λ_. x0,
                          k _. λ_. λw. abort(R x 0, w),
                          y),
                      k _. rec(y'. R x y' → R y' (S k) → R x (S k),
                               λ_. λw. abort(R x (S k), w),
                               l _. λw. λ_. w, y), z)
    in
    let Bool : U =
      ℕ / (x y. R x y,
           x. Rr x,
           x y xRy. Rs x y xRy,
           x y z xRy yRz. Rt x y z xRy yRz)
    in
    let true : Bool = π 0 in
    let false : Bool = π (S 0) in
    let if : (B :U Bool → U) → (c :U Bool) → B true → B false → B c =
      λB. λc. λt. λf.
        let congB : (x :U ℕ) → (y :U ℕ) → R x y → B (π x) ~ B (π y) =
          λx. λy. λxRy. ap(U, x. B x, (π x : Bool), π y, xRy)
        in
        let choose : (x :U ℕ) → B (π x) =
          λx. rec(x'. B (π x'), t, k _. cast(B false, B (π (S k)),
                                             congB (S 0) (S k) *,
                                             f), x)
        in
        let presTRhs : (x :U ℕ) → (y :U ℕ) → R x y → Ω =
          λx. λy. λxRy.
            (choose x) ~ cast(B (π y), B (π x), congB y x (Rs x y xRy), choose y)
        in
        let presT : (x :U ℕ) → (y :U ℕ) → Ω =
          λx. λy. (xRy :Ω R x y) → presTRhs x y xRy
        in
        let pres : (x :U ℕ) → (y :U ℕ) → presT x y =
          λx. λy. rec(x'. presT x' y,
                        rec(y'. presT 0 y',
                            λ_. refl t,
                            l _. λw. abort(presTRhs 0 (S l) w, w),
                            y),
                      k _.
                        rec(y'. presT (S k) y',
                            λw. abort(presTRhs (S k) 0 w, w),
                            l _. λ_. cast_compose (B false) (B (π (S l))) (B (π (S k)))
                                                        (congB (S 0) (S l) *)
                                                        (congB (S l) (S k) *)
                                                        f, y), x)
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
      μTy : 1 → U.
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
    let 𝔽↓T =
      μCtx : 1 → U.
        [ 'Empty : 1 → Ctx !
        ; 'Extend : (Ctx ! × Type !) → Ctx !
        ]
      functor A B f _ x =
        match x as _ return (lift [Ctx] B) ! with
        | 'Empty (_, _) → 'Empty (!, *)
        | 'Extend (Γ-τ, _) → 'Extend ((f ! (fst Γ-τ); snd Γ-τ), *)
    in
    let · : 𝔽↓T ! = 'Empty (!, *) in
    let _∷_ : 𝔽↓T ! → Type ! → 𝔽↓T ! =
      λΓ. λτ. 'Extend ((Γ; τ), *)
    in
    let Ix =
      μIx : (Type ! × 𝔽↓T !) → U.
        [ 'Ix0 : (τ-Γ : Type ! × 𝔽↓T !) → Ix (fst τ-Γ; (snd τ-Γ) ∷ (fst τ-Γ))
        ; 'IxS : (τ-Γ-τ' : Σ(τ : Type !). (Σ(Γ : 𝔽↓T !). Type ! × Ix (τ; Γ)))
          → Ix (fst τ-Γ-τ'; (fst (snd τ-Γ-τ')) ∷ (fst (snd (snd τ-Γ-τ'))))
        ]
    in
    let 𝔽↓̃τ : (𝔽↓T ! × 𝔽↓T !) → U =
      λCs.
        let Δ : 𝔽↓T ! = fst Cs in
        let Γ : 𝔽↓T ! = snd Cs in
        (τ :U Type !) → Ix (τ; Δ) → Ix (τ; Γ)
    in
    let Term =
      μTm : (Type ! × 𝔽↓T !) → U.
        [ 'Var : (τ-Γ : Σ(τ : Type !). Σ(Γ : 𝔽↓T !). Ix (τ; Γ))
          → Tm (fst τ-Γ; fst (snd τ-Γ))
        ; 'One : (Γ : 𝔽↓T !) → Tm (𝟙; Γ)
        ; 'Pair : (τ₁-τ₂-Γ : Σ(τ₁ : Type !). Σ(τ₂ : Type !).
                             Σ(Γ : 𝔽↓T !). (Tm (τ₁; Γ) × Tm (τ₂; Γ)))
          → Tm ((fst τ₁-τ₂-Γ) ✶ (fst (snd τ₁-τ₂-Γ)); fst (snd (snd τ₁-τ₂-Γ)))
        ; 'Fst : (τ₁-Γ : Σ(τ₁ : Type !). Σ(Γ : 𝔽↓T !).
                         Σ(τ₂ : Type !). Tm ((τ₁ ✶ τ₂); Γ))
          → Tm (fst τ₁-Γ; fst (snd τ₁-Γ))
        ; 'Snd : (τ₂-Γ : Σ(τ₂ : Type !). Σ(Γ : 𝔽↓T !).
                         Σ(τ₁ : Type !). Tm ((τ₁ ✶ τ₂); Γ))
          → Tm (fst τ₂-Γ; fst (snd τ₂-Γ))
        ; 'Lambda : (τ₁-τ₂-Γ : Σ(τ₁ : Type !). Σ(τ₂ : Type !).
                               Σ(Γ : 𝔽↓T !). Tm (τ₂; (Γ ∷ τ₁)))
          → Tm ((fst τ₁-τ₂-Γ) ⇒ (fst (snd τ₁-τ₂-Γ)); fst (snd (snd τ₁-τ₂-Γ)))
        ; 'App : (τ₂-Γ : Σ(τ₂ : Type !). Σ(Γ : 𝔽↓T !). Σ(τ₁ : Type !).
                         Tm ((τ₁ ⇒ τ₂); Γ) × Tm (τ₁; Γ))
          → Tm (fst τ₂-Γ; fst (snd τ₂-Γ))
        ]
    in
    let Form =
      μForm : 1 → U. ['Ne : 1 → Form !; 'Nf : 1 → Form !]
    in
    let Ne : Form ! = 'Ne (!, *) in
    let Nf : Form ! = 'Nf (!, *) in
    let Normal =
      μNormal : (Form ! × (Type ! × 𝔽↓T !)) → U.
        [ 'VVar : (τ-Γ : Σ(τ : Type !). Σ(Γ : 𝔽↓T !). Ix (τ; Γ))
          → Normal (Ne; (fst τ-Γ; fst (snd τ-Γ)))
        ; 'VOne : (Γ : 𝔽↓T !) → Normal (Nf; (𝟙;Γ))
        ; 'VPair : (τ₁-τ₂-Γ : Σ(τ₁ : Type !). Σ(τ₂ : Type !). Σ(Γ : 𝔽↓T !).
                              Normal (Nf; (τ₁; Γ)) × Normal (Nf; (τ₂; Γ)))
          → Normal (Nf; ((fst τ₁-τ₂-Γ) ✶ (fst (snd τ₁-τ₂-Γ)); fst (snd (snd τ₁-τ₂-Γ))))
        ; 'VFst : (τ₁-Γ : Σ(τ₁ : Type !). Σ(Γ : 𝔽↓T !). Σ(τ₂ : Type !).
                          Normal (Ne; (τ₁ ✶ τ₂; Γ)))
          → Normal (Ne; (fst τ₁-Γ; fst (snd τ₁-Γ)))
        ; 'VSnd : (τ₂-Γ : Σ(τ₂ : Type !). Σ(Γ : 𝔽↓T !). Σ(τ₁ : Type !).
                          Normal (Ne; (τ₁ ✶ τ₂; Γ)))
          → Normal (Ne; (fst τ₂-Γ; fst (snd τ₂-Γ)))
        ; 'VLambda : (τ₁-τ₂-Γ : Σ(τ₁ : Type !). Σ(τ₂ : Type !). Σ(Γ : 𝔽↓T !).
                                Normal (Nf; (τ₂; (Γ ∷ τ₁))))
          → Normal (Nf; ((fst τ₁-τ₂-Γ) ⇒ (fst (snd τ₁-τ₂-Γ)); fst (snd (snd τ₁-τ₂-Γ))))
        ; 'VApp : (τ₂-Γ : Σ(τ₂ : Type !). Σ(Γ : 𝔽↓T !). Σ(τ₁ : Type !).
                          Normal (Ne; (τ₁ ⇒ τ₂; Γ)) × Normal (Nf; (τ₁; Γ)))
          → Normal (Ne; (fst τ₂-Γ; fst (snd τ₂-Γ)))
        ]
    in
    let ℳ : Type ! → 𝔽↓T ! → U = λτ. λΓ. Normal (Ne; (τ; Γ)) in
    let 𝒩 : Type ! → 𝔽↓T ! → U = λτ. λΓ. Normal (Nf; (τ; Γ)) in
    let pshf : (τ :U Type !) → (Δ :U 𝔽↓T !) → ℳ τ Δ
             → (Γ :U 𝔽↓T !) → 𝔽↓̃τ (Δ; Γ) → ℳ τ Γ =
      λτ. λΔ.
        (fix [Normal as N] pshf f-τ'-Δ' v :
          let f = fst f-τ'-Δ' in
          let τ' = fst (snd f-τ'-Δ') in
          let Δ' = snd (snd f-τ'-Δ') in
          (Γ :U 𝔽↓T !) → 𝔽↓̃τ (Δ'; Γ) → Normal (f; (τ'; Γ)) =
        let f = fst f-τ'-Δ' in
        let τ' = fst (snd f-τ'-Δ') in
        let Δ' = snd (snd f-τ'-Δ') in
        λΓ. λρ.
          match v as _ return Normal (f; (τ'; Γ)) with
          | 'VVar (τ'-Δ''-ix, pf) →
            let τ' = fst τ'-Δ''-ix in
            let Δ'' = fst (snd τ'-Δ''-ix) in
            let ix = snd (snd τ'-Δ''-ix) in
            let ρ' =
              cast(𝔽↓̃τ (Δ'; Γ), 𝔽↓̃τ (Δ''; Γ),
                   ap(U, Ξ. 𝔽↓̃τ (Ξ; Γ), _, _, sym (snd (snd pf))), ρ)
            in
            'VVar ((τ'; (Γ; ρ' τ' ix)), <fst pf, <fst (snd pf), refl Γ>>)
          | 'VOne (_, pf) → 'VOne (Γ, <fst pf, <fst (snd pf), refl Γ>>)
          | 'VPair (τ₁-τ₂-Δ''-t-u, pf) →
            let τ₁ = fst τ₁-τ₂-Δ''-t-u in
            let τ₂ = fst (snd τ₁-τ₂-Δ''-t-u) in
            let Δ'' = fst (snd (snd τ₁-τ₂-Δ''-t-u)) in
            let t = fst (snd (snd (snd τ₁-τ₂-Δ''-t-u))) in
            let u = snd (snd (snd (snd τ₁-τ₂-Δ''-t-u))) in
            let ρ' =
              cast(𝔽↓̃τ (Δ'; Γ), 𝔽↓̃τ (Δ''; Γ),
                   ap(U, Ξ. 𝔽↓̃τ (Ξ; Γ), _, _, sym (snd (snd pf))), ρ)
            in
            'VPair ((τ₁; (τ₂; (Γ; (pshf (Nf; (τ₁; Δ'')) t Γ ρ';
                                   pshf (Nf; (τ₂; Δ'')) u Γ ρ')))),
                    <fst pf, <fst (snd pf), refl Γ>>)
          | 'VFst (τ₁-Δ''-τ₂-t, pf) →
            let τ₁ = fst τ₁-Δ''-τ₂-t in
            let Δ'' = fst (snd τ₁-Δ''-τ₂-t) in
            let τ₂ = fst (snd (snd τ₁-Δ''-τ₂-t)) in
            let t = snd (snd (snd τ₁-Δ''-τ₂-t)) in
            let ρ' =
              cast(𝔽↓̃τ (Δ'; Γ), 𝔽↓̃τ (Δ''; Γ),
                   ap(U, Ξ. 𝔽↓̃τ (Ξ; Γ), _, _, sym (snd (snd pf))), ρ)
            in
            'VFst ((τ₁; (Γ; (τ₂; pshf (Ne; (τ₁ ✶ τ₂; Δ'')) t Γ ρ'))),
                   <fst pf, <fst (snd pf), refl Γ>>)
          | 'VSnd (τ₂-Δ''-τ₁-t, pf) →
            let τ₂ = fst τ₂-Δ''-τ₁-t in
            let Δ'' = fst (snd τ₂-Δ''-τ₁-t) in
            let τ₁ = fst (snd (snd τ₂-Δ''-τ₁-t)) in
            let t = snd (snd (snd τ₂-Δ''-τ₁-t)) in
            let ρ' =
              cast(𝔽↓̃τ (Δ'; Γ), 𝔽↓̃τ (Δ''; Γ),
                   ap(U, Ξ. 𝔽↓̃τ (Ξ; Γ), _, _, sym (snd (snd pf))), ρ)
            in
            'VSnd ((τ₂; (Γ; (τ₁; pshf (Ne; (τ₁ ✶ τ₂; Δ'')) t Γ ρ'))),
                   <fst pf, <fst (snd pf), refl Γ>>)
          | 'VLambda (τ₁-τ₂-Δ''-t, pf) →
            let τ₁ = fst τ₁-τ₂-Δ''-t in
            let τ₂ = fst (snd τ₁-τ₂-Δ''-t) in
            let Δ'' = fst (snd (snd τ₁-τ₂-Δ''-t)) in
            let t = snd (snd (snd τ₁-τ₂-Δ''-t)) in
            let ρ' : 𝔽↓̃τ (Δ'' ∷ τ₁; Γ ∷ τ₁) =
              λτ. λix.
                match ix as _ return Ix (τ; Γ ∷ τ₁) with
                | 'Ix0 (τ''-Ξ, pf') → 'Ix0 ((fst τ''-Ξ; Γ),
                                            <fst pf', <refl Γ, snd (snd pf')>>)
                  -- pf -- 'Ix0 ((τ; Γ), <refl τ, <refl Γ, snd (snd pf')>>)
                | 'IxS (τ''-Ξ-τ'-ix, pf') →
                  let τ'' = fst τ''-Ξ-τ'-ix in
                  let Ξ = fst (snd τ''-Ξ-τ'-ix) in
                  let τ' = fst (snd (snd τ''-Ξ-τ'-ix)) in
                  let ix =
                    cast(Ix (τ''; Ξ), Ix (τ; Δ'),
                         <fst pf', fst (snd pf') ∘ snd (snd pf)>,
                         snd (snd (snd τ''-Ξ-τ'-ix)))
                  in
                  'IxS ((τ; (Γ; (τ'; ρ τ ix))), <refl τ, <refl Γ, snd (snd pf')>>)
            in
            'VLambda ((τ₁; (τ₂; (Γ; pshf (Nf; (τ₂; Δ'' ∷ τ₁)) t (Γ ∷ τ₁) ρ'))),
                      <fst pf, <fst (snd pf), refl Γ>>)
          | 'VApp (τ₂-Δ'-τ₁-t-u, pf) →
            let τ₂ = fst τ₂-Δ'-τ₁-t-u in
            let Δ'' = fst (snd τ₂-Δ'-τ₁-t-u) in
            let τ₁ = fst (snd (snd τ₂-Δ'-τ₁-t-u)) in
            let t = fst (snd (snd (snd τ₂-Δ'-τ₁-t-u))) in
            let u = snd (snd (snd (snd τ₂-Δ'-τ₁-t-u))) in
            let ρ' =
              cast(𝔽↓̃τ (Δ'; Γ), 𝔽↓̃τ (Δ''; Γ),
                   ap(U, Ξ. 𝔽↓̃τ (Ξ; Γ), _, _, sym (snd (snd pf))), ρ)
            in
            'VApp ((τ₂; (Γ; (τ₁; (pshf (Ne; (τ₁ ⇒ τ₂; Δ'')) t Γ ρ';
                                  pshf (Nf; (τ₁; Δ'')) u Γ ρ')))),
                   <fst pf, <fst (snd pf), refl Γ>>)
        ) (Ne; (τ; Δ))
    in
    let ⟦_⟧_ : Type ! → 𝔽↓T ! → U =
      (fix [Type as Ty] SemTy _ ty : 𝔽↓T ! → U = λΓ.
        match ty as _ return U with
        | 'Unit (_, _) → 1
        | 'Product (p, _) →
          let τ₁ = fst p in
          let τ₂ = snd p in
          SemTy ! τ₁ Γ × SemTy ! τ₂ Γ
        | 'Function (f, _) →
          let τ₁ = fst f in
          let τ₂ = snd f in
          (Δ :U 𝔽↓T !) → 𝔽↓̃τ (Γ; Δ) → SemTy ! τ₁ Δ → SemTy ! τ₂ Δ) !
    in
    let Π : 𝔽↓T ! → 𝔽↓T ! → U =
      (fix [𝔽↓T as Ctx] Env _ Γ : 𝔽↓T ! → U = λΔ.
        match Γ as _ return U with
        | 'Empty (_, _) → 1
        | 'Extend (Γ-τ, _) →
          let Γ = fst Γ-τ in
          let τ = snd Γ-τ in
          Env ! Γ Δ × ⟦ τ ⟧ Δ) !
    in
    let rn : (Γ :U 𝔽↓T !) → (Δ :U 𝔽↓T !) → 𝔽↓̃τ (Δ; Γ) → (τ :U Type !)
           → ⟦ τ ⟧ Δ → ⟦ τ ⟧ Γ =
      λΓ. λΔ. λρ.
        (fix [Type as Ty view ι] rn _ τ : ⟦ (ι ! τ) ⟧ Δ → ⟦ (ι ! τ) ⟧ Γ =
          match τ as τ' return
            let τ' : Type ! = in (fmap[Type](Ty, Type, ι, !, τ')) in
            ⟦ τ' ⟧ Δ → ⟦ τ' ⟧ Γ
          with
          | 'Unit (_, _) → λ_. !
          | 'Product (τ₁-τ₂, _) →
            let τ₁ = fst τ₁-τ₂ in
            let τ₂ = snd τ₁-τ₂ in
            λpair.
              let t = fst pair in
              let u = snd pair in
              (rn ! τ₁ (fst pair); rn ! τ₂ (snd pair))
          | 'Function (τ₁-τ₂, _) →
            let τ₁ = fst τ₁-τ₂ in
            let τ₂ = snd τ₁-τ₂ in
            λf. λΔ'. λρ'. f Δ' (λχ. λix. ρ' χ (ρ χ ix))) !
    in
    let lookup : (τ :U Type !) → (Γ :U 𝔽↓T !) → Ix (τ; Γ)
               → (Δ :U 𝔽↓T !) → Π Γ Δ → ⟦ τ ⟧ Δ =
      λτ. λΓ.
      (fix [Ix as I] lookup τ-Γ ix : (Δ :U 𝔽↓T !) → Π (snd τ-Γ) Δ → ⟦ (fst τ-Γ) ⟧ Δ =
        let τ = fst τ-Γ in
        let Γ = snd τ-Γ in
        λΔ. λenv.
          match ix as _ return ⟦ τ ⟧ Δ with
          | 'Ix0 (τ'-Γ', pf) →
            let Γ' = snd τ'-Γ' in
            let env-cast =
              cast(Π Γ Δ, Π (Γ' ∷ τ) Δ, ap(U, Ξ. Π Ξ Δ, _, Γ' ∷ τ, sym (snd pf)), env)
            in
            snd env-cast
          | 'IxS (τ'-Γ'-τ''-ix, pf) →
            let τ' = fst τ'-Γ'-τ''-ix in
            let Γ' = fst (snd τ'-Γ'-τ''-ix) in
            let τ'' = fst (snd (snd τ'-Γ'-τ''-ix)) in
            let ix = snd (snd (snd τ'-Γ'-τ''-ix)) in
            let ix' =
              cast(I (τ'; Γ'), I (τ; Γ'), ap(U, χ. I (χ; Γ'), _, _, fst pf), ix)
            in
            let env-cast =
              cast(Π Γ Δ, Π (Γ' ∷ τ') Δ, ap(U, Ξ. Π Ξ Δ, _, Γ' ∷ τ', sym (snd pf)), env)
            in
            lookup (τ; Γ') ix' Δ (fst env-cast)) (τ; Γ)
    in
    let __⟦_⟧__ : (Γ :U 𝔽↓T !) → (τ :U Type !) → Term (τ; Γ)
                → (Δ :U 𝔽↓T !) → Π Γ Δ → ⟦ τ ⟧ Δ =
      λΓ. λτ.
      (fix [Term as Tm ] eval τ-Γ tm : (Δ :U 𝔽↓T !) → Π (snd τ-Γ) Δ → ⟦ (fst τ-Γ) ⟧ Δ =
        let τ = fst τ-Γ in
        let Γ = snd τ-Γ in
        λΔ. λenv.
          match tm as _ return ⟦ τ ⟧ Δ with
          | 'Var (τ'-Γ'-ix, pf) →
            let τ' = fst τ'-Γ'-ix in
            let Γ' = fst (snd τ'-Γ'-ix) in
            let ix = snd (snd τ'-Γ'-ix) in
            let env' =
              cast(Π Γ Δ, Π Γ' Δ, ap(U, Ξ. Π Ξ Δ, _, _, sym (snd pf)), env)
            in
            cast(⟦ τ' ⟧ Δ, ⟦ τ ⟧ Δ,
                 ap(U, τ''. ⟦ τ'' ⟧ Δ, _, _, fst pf), lookup τ' Γ' ix Δ env')
          | 'One (_, pf) → cast(1, ⟦ τ ⟧ Δ, ap(U, τ'. ⟦ τ' ⟧ Δ, 𝟙, τ, fst pf), !)
          | 'Pair (τ₁-τ₂-Γ'-t-u, pf) →
            let τ₁ = fst τ₁-τ₂-Γ'-t-u in
            let τ₂ = fst (snd τ₁-τ₂-Γ'-t-u) in
            let Γ' = fst (snd (snd τ₁-τ₂-Γ'-t-u)) in
            let t = fst (snd (snd (snd τ₁-τ₂-Γ'-t-u))) in
            let u = snd (snd (snd (snd τ₁-τ₂-Γ'-t-u))) in
            let env' =
              cast(Π Γ Δ, Π Γ' Δ, ap(U, Ξ. Π Ξ Δ, _, _, sym (snd pf)), env)
            in
            let vt : ⟦ τ₁ ⟧ Δ =
              eval (τ₁; Γ') t Δ env'
            in
            let vu : ⟦ τ₂ ⟧ Δ =
              eval (τ₂; Γ') u Δ env'
            in
            cast(⟦ τ₁ ⟧ Δ × ⟦ τ₂ ⟧ Δ, ⟦ τ ⟧ Δ,
                 ap(U, τ'. ⟦ τ' ⟧ Δ, τ₁ ✶ τ₂, τ, fst pf), (vt; vu))
          | 'Fst (τ₁-Γ'-τ₂-t, pf) →
            let τ₁ = fst τ₁-Γ'-τ₂-t in
            let Γ' = fst (snd τ₁-Γ'-τ₂-t) in
            let τ₂ = fst (snd (snd τ₁-Γ'-τ₂-t)) in
            let t = snd (snd (snd τ₁-Γ'-τ₂-t)) in
            let env' =
              cast(Π Γ Δ, Π Γ' Δ, ap(U, Ξ. Π Ξ Δ, _, _, sym (snd pf)), env)
            in
            let vt : ⟦ τ₁ ⟧ Δ × ⟦ τ₂ ⟧ Δ =
              eval (τ₁ ✶ τ₂; Γ') t Δ env'
            in
            cast(⟦ τ₁ ⟧ Δ, ⟦ τ ⟧ Δ, ap(U, τ'. ⟦ τ' ⟧ Δ, _, _, fst pf), fst vt)
          | 'Snd (τ₂-Γ'-τ₁-t, pf) →
            let τ₂ = fst τ₂-Γ'-τ₁-t in
            let Γ' = fst (snd τ₂-Γ'-τ₁-t) in
            let τ₁ = fst (snd (snd τ₂-Γ'-τ₁-t)) in
            let t = snd (snd (snd τ₂-Γ'-τ₁-t)) in
            let env' =
              cast(Π Γ Δ, Π Γ' Δ, ap(U, Ξ. Π Ξ Δ, _, _, sym (snd pf)), env)
            in
            let vt : ⟦ τ₁ ⟧ Δ × ⟦ τ₂ ⟧ Δ =
              eval (τ₁ ✶ τ₂; Γ') t Δ env'
            in
            cast(⟦ τ₂ ⟧ Δ, ⟦ τ ⟧ Δ, ap(U, τ'. ⟦ τ' ⟧ Δ, _, _, fst pf), snd vt)
          | 'Lambda (τ₁-τ₂-Γ'-t, pf) →
            let τ₁ = fst τ₁-τ₂-Γ'-t in
            let τ₂ = fst (snd τ₁-τ₂-Γ'-t) in
            let Γ' = fst (snd (snd τ₁-τ₂-Γ'-t)) in
            let t = snd (snd (snd τ₁-τ₂-Γ'-t)) in
            let env' =
              cast(Π Γ Δ, Π Γ' Δ, ap(U, Ξ. Π Ξ Δ, _, _, sym (snd pf)), env)
            in
            let Λt : (Δ' :U 𝔽↓T !) → 𝔽↓̃τ (Δ; Δ') → ⟦ τ₁ ⟧ Δ' → ⟦ τ₂ ⟧ Δ' =
              λΔ'. λf. λχ.
                let rn-env : (Ξ :U 𝔽↓T !) → Π Ξ Δ → 𝔽↓̃τ (Δ; Δ') → Π Ξ Δ' =
                  (fix [𝔽↓T as Ctx view ι] rn-env _ Ξ : Π (ι ! Ξ) Δ → 𝔽↓̃τ (Δ; Δ')
                                                      → Π (ι ! Ξ) Δ' =
                    match Ξ as Ξ' return
                      let Ξ'' : 𝔽↓T ! = in (fmap[𝔽↓T](Ctx, 𝔽↓T, ι, !, Ξ')) in
                      Π Ξ'' Δ → 𝔽↓̃τ (Δ; Δ') → Π Ξ'' Δ'
                    with
                    | 'Empty (_, _) → λ_. λ_. !
                    | 'Extend (Ξ'-τ', _) →
                      let Ξ' = fst Ξ'-τ' in
                      let τ' = snd Ξ'-τ' in
                      λε-χ. λρ. (rn-env ! Ξ' (fst ε-χ) ρ; rn Δ' Δ ρ τ' (snd ε-χ))) !
                in
                eval (τ₂; Γ' ∷ τ₁) t Δ' (rn-env Γ' env' f; χ)
            in
            cast ((Δ' :U 𝔽↓T !) → 𝔽↓̃τ (Δ; Δ') → ⟦ τ₁ ⟧ Δ' → ⟦ τ₂ ⟧ Δ', ⟦ τ ⟧ Δ,
                  ap(U, τ'. ⟦ τ' ⟧ Δ, τ₁ ⇒ τ₂, _, fst pf), Λt)
          | 'App (τ₂-Γ'-τ₁-t-u, pf) →
            let τ₂ = fst τ₂-Γ'-τ₁-t-u in
            let Γ' = fst (snd τ₂-Γ'-τ₁-t-u) in
            let τ₁ = fst (snd (snd τ₂-Γ'-τ₁-t-u)) in
            let t = fst (snd (snd (snd τ₂-Γ'-τ₁-t-u))) in
            let u = snd (snd (snd (snd τ₂-Γ'-τ₁-t-u))) in
            let env' =
              cast(Π Γ Δ, Π Γ' Δ, ap(U, Ξ. Π Ξ Δ, _, _, sym (snd pf)), env)
            in
            let val : ⟦ τ₂ ⟧ Δ =
              (eval (τ₁ ⇒ τ₂; Γ') t Δ env') Δ (λ_. λx. x) (eval (τ₁; Γ') u Δ env')
            in
            cast(⟦ τ₂ ⟧ Δ, ⟦ τ ⟧ Δ, ap(U, τ'. ⟦ τ' ⟧ Δ, _, _, fst pf), val)) (τ; Γ)
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
              let τ₁ = fst τ₁-τ₂ in
              let τ₂ = snd τ₁-τ₂ in
              λm. (u τ₁ Γ ('VFst ((ι ! τ₁; (Γ; (ι ! τ₂; m))),
                                  refl ((Ne; (ι ! τ₁; Γ)) : Form ! × (Type ! × 𝔽↓T !))));
                   u τ₂ Γ ('VSnd ((ι ! τ₂; (Γ; (ι ! τ₁; m))),
                                  refl ((Ne; (ι ! τ₂; Γ)) : Form ! × (Type ! × 𝔽↓T !)))))
            | 'Function (τ₁-τ₂, _) →
              let τ₁ = fst τ₁-τ₂ in
              let τ₂ = snd τ₁-τ₂ in
              let τ₁⇒τ₂ : Type ! = (ι ! τ₁) ⇒ (ι ! τ₂) in
              λm. λΔ. λρ. λχ.
                u τ₂ Δ ('VApp ((ι ! τ₂; (Δ; (ι ! τ₁; (pshf τ₁⇒τ₂ Γ m Δ ρ; q τ₁ Δ χ)))),
                               refl ((Ne; (ι ! τ₂; Δ)) : Form ! × (Type ! × 𝔽↓T !))))
            )
          -- Quote
          | 'Nf (_, _) →
            (match τ as τ return
              let τ' : Type ! = in (fmap[Type](Ty, Type, ι, !, τ)) in
              ⟦ τ' ⟧ Γ → 𝒩 τ' Γ
            with
            | 'Unit (_, _) → λ_. 'VOne (Γ, <*, <*, refl Γ>>)
            | 'Product (τ₁-τ₂, _) →
              let τ₁ = fst τ₁-τ₂ in
              let τ₂ = snd τ₁-τ₂ in
              λp.
                let t = fst p in
                let u = snd p in
                'VPair ((ι ! τ₁; (ι ! τ₂; (Γ; (q τ₁ Γ t; q τ₂ Γ u)))),
                        <*, <<refl (ι ! τ₁), refl (ι ! τ₂)>, refl Γ>>)
            | 'Function (τ₁-τ₂, _) →
              let τ₁ = fst τ₁-τ₂ in
              let τ₁' = ι ! τ₁ in
              let τ₂ = snd τ₁-τ₂ in
              let τ₂' = ι ! τ₂ in
              λf.
                let χ : ⟦ τ₁' ⟧ (Γ ∷ τ₁') =
                  u τ₁ (Γ ∷ τ₁') ('VVar ((τ₁'; (Γ ∷ τ₁'; 'Ix0 ((τ₁'; Γ),
                                                               <refl τ₁', <refl Γ, refl τ₁'>>))),
                                  <*, <refl τ₁', <refl Γ, refl τ₁'>>>))
                in
                let ↑ : 𝔽↓̃τ (Γ; Γ ∷ τ₁') =
                  λτ'. λixΓ. 'IxS ((τ'; (Γ; (τ₁'; ixΓ))), <refl τ', <refl Γ, refl τ₁'>>)
                in
                'VLambda ((τ₁'; (τ₂'; (Γ; q τ₂ (Γ ∷ τ₁') (f (Γ ∷ τ₁') ↑ χ)))),
                          <*, <<refl τ₁', refl τ₂'>, refl Γ>>))) ! τ
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
              let Γ' = fst Γ'-τ in
              let Γ'' = ι ! Γ' in
              let τ = snd Γ'-τ in
              let χ : ⟦ τ ⟧ (Γ'' ∷ τ) =
                u τ (Γ'' ∷ τ) ('VVar ((τ; (Γ'' ∷ τ; 'Ix0 ((τ; Γ''),
                                                          <refl τ, <refl Γ'', refl τ>>))),
                                      <*, <refl τ, <refl Γ'', refl τ>>>))
              in
              let shift : (Δ :U 𝔽↓T !) → Π Δ Γ'' → Π Δ (Γ'' ∷ τ) =
                (fix [𝔽↓T as Ctx view ι] shift _ Δ : Π (ι ! Δ) Γ'' → Π (ι ! Δ) (Γ'' ∷ τ) =
                  match Δ as Δ return
                    let Δ' : 𝔽↓T ! = in (fmap[𝔽↓T](Ctx, 𝔽↓T, ι, !, Δ)) in
                    Π Δ' Γ'' → Π Δ' (Γ'' ∷ τ)
                  with
                  | 'Empty (_, _) → λ_. !
                  | 'Extend (Δ'-τ', _) →
                    let Δ' = fst Δ'-τ' in
                    let τ' = snd Δ'-τ' in
                    let ↑ : 𝔽↓̃τ (Γ''; Γ'' ∷ τ) =
                      λτ''. λixΓ''.
                        'IxS ((τ''; (Γ''; (τ; ixΓ''))), <refl τ'', <refl Γ'', refl τ>>)
                    in
                    λenv. (shift ! Δ' (fst env); rn (Γ'' ∷ τ) Γ'' ↑ τ' (snd env))
                ) !
              in
              (shift (ι ! Γ') (xs ! Γ'); χ)
            ) ! Γ
        in
        q τ Γ (Γ τ ⟦ t ⟧ Γ xs)
    in
    nbe 𝟙 · ('App ((𝟙; (·; (𝟙;
                   ('Lambda ((𝟙; (𝟙; (·;
                             'Var ((𝟙; (· ∷ 𝟙; 'Ix0 ((𝟙; ·), <*, <*, *>>))),
                                   <*, <*, *>>)))),
                             <<*, *>, *>);
                   'One (·, <*, *>))))),
             <*, *>))
  |]

natWithInfinity :: String
natWithInfinity =
  [r|
    let Nats' =
      μNats' : 1 → U.
        [ '0 : 1 → Nats' !
        ; 'S : Nats' ! → Nats' !
        ; '∞ : 1 → Nats' !
        ]
        functor A B f _ x =
          match x as _ return (lift[Nats'] B) ! with
          | '0 (_, _) → '0 (!, *)
          | 'S (n, _) → 'S (f ! n, *)
          | '∞ (_, _) → '∞ (!, *)
    in
    let succ-∞ : Nats' ! → Ω =
      (fix [Nats' as N] succ-∞ _ n : Ω =
        match n as _ return Ω with
        | '0 (_, _) → ⊥
        | 'S (n, _) → succ-∞ ! n
        | '∞ (_, _) → ⊤) !
    in
    let R : Nats' ! → Nats' ! → Ω =
      (fix [Nats' as N view ι] R _ x : Nats' ! → Ω =
        match x as _ return Nats' ! → Ω with
        | '0 (_, _) → λy.
          (match y as _ return Ω with
          | '0 (_, _) → ⊤
          | 'S (_, _) → ⊥
          | '∞ (_, _) → ⊥)
        | 'S (n, _) → λy.
          (match y as _ return Ω with
          | '0 (_, _) → ⊥
          | 'S (m, _) → R ! n m
          | '∞ (_, _) → succ-∞ (ι ! n))
        | '∞ (_, _) → succ-∞) !
    in
    let Rr : (x :U Nats' !) → R x x =
      (fix [Nats' as N view ι] Rr _ x : R (ι ! x) (ι ! x) =
        match x as x' return
          let x' : Nats' ! = in (fmap[Nats'](N, Nats', ι, !, x')) in
          R x' x'
        with
        | '0 (_, _) → *
        | 'S (n, _) → Rr ! n
        | '∞ (_, _) → *) !
    in
    let Rs : (x :U Nats' !) → (y :U Nats' !) → R x y → R y x =
      (fix [Nats' as N view ι] Rs _ x : (y :U Nats' !) → R (ι ! x) y → R y (ι ! x) =
        match x as x' return
          let x' : Nats' ! = in (fmap[Nats'](N, Nats', ι, !, x')) in
          (y :U Nats' !) → R x' y → R y x'
        with
        | '0 (_, _) → λy.
          (match y as y' return R ('0 (!, *)) y' → R y' ('0 (!, *)) with
          | '0 (_, _) → λp. p
          | 'S (_, _) → λp. p
          | '∞ (_, _) → λp. p)
        | 'S (n, _) → λy.
          (match y as y' return R ('S (ι ! n, *)) y' → R y' ('S (ι ! n, *)) with
          | '0 (_, _) → λp. p
          | 'S (m, _) → Rs ! n m
          | '∞ (_, _) → λp. p)
        | '∞ (_, _) → λy.
          (match y as y' return R ('∞ (!, *)) y' → R y' ('∞ (!, *)) with
          | '0 (_, _) → λp. p
          | 'S (_, _) → λp. p
          | '∞ (_, _) → λp. p)
          ) !
    in
    let trans-∞ : (x :U Nats' !) → (y :U Nats' !) → succ-∞ x → R x y → succ-∞ y =
      (fix [Nats' as N view ι] trans-∞ _ x : (y :U Nats' !) → succ-∞ (ι ! x) → R (ι ! x) y → succ-∞ y =
        λy.
          match x as x' return
            let x' : Nats' ! = in (fmap[Nats'](N, Nats', ι, !, x')) in
            succ-∞ x' → R x' y → succ-∞ y
          with
          | '0 (_, _) → λp. λ_. abort(succ-∞ y, p)
          | 'S (n, _) →
            (match y as y' return succ-∞ ('S (ι ! n, *)) → R ('S (ι ! n, *)) y' → succ-∞ y' with
            | '0 (_, _) → λ_. λp. p
            | 'S (m, _) → trans-∞ ! n m
            | '∞ (_, _) → λ_. λ_. *
            )
          | '∞ (_, _) → λ_. λp. p) !
    in
    let succ-implies-R : (x :U Nats' !) → (y :U Nats' !) → succ-∞ x → succ-∞ y → R x y =
      (fix [Nats' as N view ι] succ-implies-R _ x : (y :U Nats' !) → succ-∞ (ι ! x) → succ-∞ y → R (ι ! x) y =
        λy.
          match x as x' return
            let x' : Nats' ! = in (fmap[Nats'](N, Nats', ι, !, x')) in
            succ-∞ x' → succ-∞ y → R x' y
          with
          | '0 (_, _) → λp. λ_. abort(R ('0 (!, *)) y, p)
          | 'S (n, _) →
            (match y as y' return succ-∞ ('S (ι ! n, *)) → succ-∞ y' → R ('S (ι ! n, *)) y' with
            | '0 (_, _) → λ_. λp. p
            | 'S (m, _) → succ-implies-R ! n m
            | '∞ (_, _) → λp. λ_. p
            )
          | '∞ (_, _) → λ_. λp. p) !
    in
    let Rt : (x :U Nats' !) → (y :U Nats' !) → (z :U Nats' !) → R x y → R y z → R x z =
      (fix [Nats' as N view ι] Rt _ x : (y :U Nats' !) → (z :U Nats' !) → R (ι ! x) y → R y z → R (ι ! x) z =
        match x as x' return
          let x' : Nats' ! = in (fmap[Nats'](N, Nats', ι, !, x')) in
          (y :U Nats' !) → (z :U Nats' !) → R x' y → R y z → R x' z
        with
        | '0 (_, _) → λy.
          (match y as y' return (z :U Nats' !) → R ('0 (!, *)) y' → R y' z → R ('0 (!, *)) z with
          | '0 (_, _) → λz. λ_. λp. p
          | 'S (_, _) → λz. λp. λ_. abort(R ('0 (!, *)) z, p)
          | '∞ (_, _) → λz. λp. λ_. abort(R ('0 (!, *)) z, p)
          )
        | 'S (n, _) → λy.
          (match y as y' return (z :U Nats' !) → R ('S (ι ! n, *)) y' → R y' z → R ('S (ι ! n, *)) z with
          | '0 (_, _) → λz. λp. λ_. abort(R ('S (ι ! n, *)) z, p)
          | 'S (m, _) → λz.
            (match z as z' return R ('S (ι ! n, *)) ('S (m, *)) → R ('S (m, *)) z' → R ('S (ι ! n, *)) z' with
            | '0 (_, _) → λ_. λp. p
            | 'S (k, _) → Rt ! n m k
            | '∞ (_, _) → λp. λq. trans-∞ m (ι ! n) q (Rs (ι ! n) m p)
            )
          | '∞ (_, _) → λz.
            (match z as z' return R ('S (ι ! n, *)) ('∞ (!, *)) → R ('∞ (!, *)) z' → R ('S (ι ! n, *)) z' with
            | '0 (_, _) → λ_. λp. p
            | 'S (m, _) → succ-implies-R (ι ! n) m
            | '∞ (_, _) → λp. λ_. p
            )
          )
        | '∞ (_, _) → λy.
          (match y as y' return (z :U Nats' !) → R ('∞ (!, *)) y' → R y' z → R ('∞ (!, *)) z with
          | '0 (_, _) → λz. λp. λ_. abort(succ-∞ z, p)
          | 'S (n, _) → λz.
            (match z as z' return R ('∞ (!, *)) ('S (n, *)) → R ('S (n, *)) z' → R ('∞ (!, *)) z' with
            | '0 (_, _) → λ_. λp. abort(R ('∞ (!, *)) ('0 (!, *)), p)
            | 'S (m, _) → trans-∞ n m
            | '∞ (_, _) → λ_. λ_. Rr ('∞ (!, *))
            )
          | '∞ (_, _) → λz. λ_. λp. p
          )
      ) !
    in
    let Nats =
      (Nats' !) / (x y. R x y, x. Rr x, x y xRy. Rs x y xRy, x y z xRy yRz. Rt x y z xRy yRz)
    in
    let succ : Nats → Nats =
      λn. Q-elim(_. Nats, n. π ('S (n, *)), _ _ e. e, n)
    in
    let fromNat : ℕ → Nats =
      λn. rec(_. Nats, π ('0 (!, *)), _ k. succ k, n)
    in
    let ∞ : Nats = π ('∞ (!, *)) in
    fromNat (S (S 0))
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
