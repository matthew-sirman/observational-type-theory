{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Error
import Eval
import MonadChecker

import Parser.Parser
import PrettyPrinter

import TypeChecker

import Control.Monad.Except
import Control.Monad.State
import Data.Function ((&))
import Data.Functor.Identity

import Control.Monad.Oops
import Error.Diagnose

import Text.RawString.QQ

stlcInterpreter :: String
stlcInterpreter =
  [r|
    let Type : [⊤] → U =
      μTy : [⊤] → U. λ_.
        [ 'Unit : ⊤ → Ty <*>
        ; 'Product : (Ty <*> × Ty <*>) → Ty <*>
        ; 'Function : (Ty <*> × Ty <*>) → Ty <*>
        ]
    in
    let 1 : Type <*> = 'Unit (*, *) in
    let _✶_ : Type <*> → Type <*> → Type <*> =
      λt. λu. 'Product ((t; u), *)
    in
    let _⇒_ : Type <*> → Type <*> → Type <*> =
      λdom. λcod. 'Function ((dom; cod), *)
    in
    let 𝔽↓T : [⊤] → U =
      μCtx : [⊤] → U. λ_. ['Empty : ⊤ → Ctx <*>; 'Extend : (Ctx <*> × Type <*>) → Ctx <*>]
    in
    let · : 𝔽↓T <*> = 'Empty (*, *) in
    let _∷_ : 𝔽↓T <*> → Type <*> -> 𝔽↓T <*> =
      λΓ. λτ. 'Extend ((Γ; τ), *)
    in
    let Ix : (Type <*> × 𝔽↓T <*>) → U =
      μIx : (Type <*> × 𝔽↓T <*>) → U. λτ_Γ.
        [ 'Ix0 : (Γ' :U 𝔽↓T <*>) → Ix (fst τ_Γ; Γ' ∷ (fst τ_Γ))
        ; 'IxS : (τ'_Γ' :U Type <*> × (Σ(Γ' : 𝔽↓T <*>). Ix (fst τ_Γ; Γ'))) → Ix (fst τ_Γ; (fst (snd τ'_Γ')) ∷ (fst τ'_Γ'))
        ]
    in
    let 𝔽↓̃τ : (𝔽↓T <*> × 𝔽↓T <*>) → U =
      λCs.
        let Δ : 𝔽↓T <*> = fst Cs in
        let Γ : 𝔽↓T <*> = snd Cs in
        (τ :U Type <*>) → Ix (τ; Δ) → Ix (τ; Γ)
    in
    let Term : (Type <*> × 𝔽↓T <*>) → U =
      μTm : (Type <*> × 𝔽↓T <*>) → U. λτ_Γ.
        [ 'Var : (Ix τ_Γ) → Tm τ_Γ
        ; 'One : ⊤ → Tm (1; snd τ_Γ)
        ; 'Pair : (τ₁_τ₂ :U Σ(τ₁ : Type <*>). Σ(τ₂ : Type <*>). (Tm (τ₁; snd τ_Γ) × Tm (τ₂; snd τ_Γ))) → Tm ((fst τ₁_τ₂) ✶ (fst (snd τ₁_τ₂)); snd τ_Γ)
        ; 'Fst : (Σ(τ₂ : Type <*>). Tm (((fst τ_Γ) ✶ τ₂); snd τ_Γ)) → Tm τ_Γ
        ; 'Snd : (Σ(τ₁ : Type <*>). Tm ((τ₁ ✶ (fst τ_Γ)); snd τ_Γ)) → Tm τ_Γ
        ; 'Lambda : (τ₁_τ₂ :U Σ(τ₁ : Type <*>). Σ(τ₂ : Type <*>). Tm (τ₂; ((snd τ_Γ) ∷ τ₁))) → Tm ((fst τ₁_τ₂) ⇒ (fst (snd τ₁_τ₂)); snd τ_Γ)
        ; 'App : (Σ(τ₁ : Type <*>). Tm ((τ₁ ⇒ (fst τ_Γ)); snd τ_Γ) × Tm (τ₁; snd τ_Γ)) → Tm τ_Γ
        ]
    in
    -- let Vec : U → ℕ → U =
    --   λA. μVec : ℕ → U. λn. ['Nil : [n ~ 0]; 'Cons : Σ(m : ℕ). [S m ~ n] × (A × Vec m)]
    -- in
    let Form : [⊤] → U =
      μForm : [⊤] → U. λ_. ['Ne : ⊤ → Form <*>; 'Nf : ⊤ → Form <*>]
    in
    let ℳ : Form <*> = 'Ne (*, *) in
    -- let 𝒩 : Form <*> = 'Nf (*, *) in
    -- let Val : (Form <*> × (Type <*> × 𝔽↓T <*>)) → U =
    --   μVal : (Form <*> × (Type <*> × 𝔽↓T <*>)) → U. λf_τ_Γ.
    --     [ 'VVar : Ix (snd f_τ_Γ) → Val (ℳ; snd f_τ_Γ)
    --     ; 'VOne : ⊤ → Val (𝒩; (1; snd (snd f_τ_Γ)))
    --     ; 'VPair : (τ₁_τ₂ :U Σ(τ₁ : Type <*>). Σ(τ₂ : Type <*>). (Val (𝒩; (τ₁; snd (snd f_τ_Γ))) × Val (𝒩; (τ₂; snd (snd f_τ_Γ))))) → Val (𝒩; ((fst τ₁_τ₂) ✶ (fst (snd τ₁_τ₂)); snd (snd f_τ_Γ)))
    --     ; 'VFst : (Σ(τ₂ : Type <*>). Val (ℳ; ((fst (snd f_τ_Γ)) ✶ τ₂; snd (snd f_τ_Γ)))) → Val (ℳ; snd f_τ_Γ)
    --     ; 'VSnd : (Σ(τ₁ : Type <*>). Val (ℳ; (τ₁ ✶ (fst (snd f_τ_Γ)); snd (snd f_τ_Γ)))) → Val (ℳ; snd f_τ_Γ)
    --     ; 'VLambda : (τ₁_τ₂ :U Σ(τ₁ : Type <*>). Σ(τ₂ : Type <*>). Val (𝒩; (τ₂; ((snd (snd f_τ_Γ)) ∷ τ₁)))) → Val (𝒩; ((fst τ₁_τ₂) ⇒ (fst (snd τ₁_τ_2)); snd (snd f_τ_Γ)))
    --     ; 'VApp : (Σ(τ₁ : Type <*>). Val (ℳ; (τ₁ ⇒ (fst (snd f_τ_Γ)); snd (snd f_τ_Γ))) × Val (𝒩; (τ₁; snd (snd f_τ_Γ)))) → Val (ℳ; snd f_τ_Γ)
    --     ]
    -- in
    -- let ⟦_⟧_ : Type <*> → 𝔽↓T <*> → U =
    --   fix [Type as Ty] SemTy _ ty : 𝔽↓T <*> → U = λΓ.
    --     match ty as _ return U with
    --     | 'Unit (_, _) → [⊤]
    --     | 'Product (p, _) →
    --       let τ₁ : Ty <*> = fst p in
    --       let τ₂ : Ty <*> = snd p in
    --       SemTy τ₁ Γ × SemTy τ₂ Γ
    --     | 'Function (f, _) →
    --       let τ₁ : Ty <*> = fst f in
    --       let τ₂ : Ty <*> = snd f in
    --       (Δ :U Context) → 𝔽↓̃τ (G; D) → SemTy τ₁ Δ → SemTy τ₂ Δ
    -- in
    -- let Env : Context → Context → U =
    --   fix [Context as Ctx] Env G : Context → U = λD.
    --     match G as _ return U with
    --     | 'Empty _ → [⊤]
    --     | 'Extend G_T →
    --       let G : Ctx = fst G_T in
    --       let T : Type = snd G_T in
    --       Env G D × SemTy T D
    -- in
    -- let lookup : (T :U Type) → (G :U Context) → Ix T G → (D :U Context) → Env G D → SemTy T D =
    --   fix [Ix as I] lookup T G ix : (D :U Context) → Env G D → SemTy T D =
    --     λD. λenv.
    --       match ix as _ return SemTy T D with
    --       | 'Ix0 x0 →
    --         let G' : Context = fst x0 in
    --         let extension : G ~[Context] 'Extend (G'; T) = ▢-elim(snd x0) in
    --         -- Needs better casting for fixed points.
    --         fst (cast(Env G D, Env ('Extend (G'; T)) D, 0, env))
    --       -- | 'IxS xS →
    --       --   let G' : Context = fst (snd xS) in
    --       --   let ix' : I T G' = snd (snd (snd xS)) in
    --       --   lookup T G' ix' D (snd env)
    -- in
    -- let eval : (T :U Type) → (G :U Context) → Term T G → (D :U Context) → Env G D → SemTy T D =
    --   fix [Term as Tm] eval T G tm : (D :U Context) → Env G D → SemTy T D =
    --     λD. λenv.
    --       match tm as _ return SemTy T D with
    --       | 'Var x → lookup T G D x env
    -- in
    -- let Env : ℕ → U = Vec (Val Nf) in
    -- let lookup : (n :_ ℕ) → Env n → Ix n → Val Nf =
    --   fix [Env as E] lookup n env : Ix n → Val Nf =
    --     match env as _ return Ix n → Val Nf with
    --       | 'Nil n_eq_0 →
    --         λix.
    --           (match ix as _ return Val ('Nf <*>) with
    --             | 'Ix0 x0 →
    --               let m : ℕ = fst x0 in
    --               let s_m_eq_n : S m ~ n = ▢-elim(snd x0) in
    --               abort(Val Nf, trans(S m, n, 0, s_m_eq_n, ▢-elim(n_eq_0)))
    --             | 'IxS xS →
    --               let m : ℕ = fst xS in
    --               let s_m_eq_n : S m ~ n = ▢-elim (fst (snd xS)) in
    --               abort(Val Nf, trans(S m, n, 0, s_m_eq_n, ▢-elim(n_eq_0)))
    --           )
    --       | 'Cons ls →
    --         let m : ℕ = fst ls in
    --         let s_m_eq_n : S m ~ n = ▢-elim(fst (snd ls)) in
    --         let a : Val Nf = fst (snd (snd ls)) in
    --         let tl : E m = snd (snd (snd ls)) in
    --         λix.
    --           (match ix as _ return Val Nf with
    --             | 'Ix0 _ → a
    --             | 'IxS ix' →
    --               let k : ℕ = fst ix' in
    --               let s_k_eq_n : S k ~ n = ▢-elim(fst (snd ix')) in
    --               let ix' : Ix k = snd (snd ix') in
    --               let k_eq_m : k ~ m = trans(S k, n, S m, s_k_eq_n, sym(S m, n, s_m_eq_n)) in
    --               lookup m tl (cast_ix _ _ k_eq_m ix')
    --           )
    -- in
    -- let eval : (n :U ℕ) → Term n → Env n → Val Nf =
    --   fix [Term as Tm] eval n tm : Env n → Val Nf =
    --     λenv.
    --       match tm as _ return Val Nf with
    --         | 'Var x → lookup n env x
    --         | 'One _ → 'VOne <refl Nf>
    --         | 'Pair p →
    --           let t : Tm n = fst p in
    --           let u : Tm n = snd p in
    --           'VPair (<refl Nf>; (eval n t env; eval n u env))
    --         | 'Fst p →
    --           (match eval n p env as _ return Val Nf with
    --             | 'VVar x → abort(Val Nf, ▢-elim(fst x))
    --             | 'VOne x → not well typed.....
    --             | 'VFst p → abort(Val Nf, ▢-elim(fst p))
    --             | 'VSnd p → abort(Val Nf, ▢-elim(fst p))
    --             | 'VPair p → fst (snd p)
    --             |
    --           )
    -- in
    *
  |]

main :: IO ()
main = do
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
    Right (t, tty, _) -> do
      putStrLn "Program:"
      putStrLn (prettyPrintTerm [] t)
      putStrLn "\nHas type:"
      putStrLn (prettyPrintTerm [] (runEvaluator (quote 0 tty) (_metaCtx mctx)))
      putStrLn "\nReduces to:"
      putStrLn (prettyPrintTerm [] (runEvaluator (nbe [] t) (_metaCtx mctx)))
    Left () -> pure ()
  where
    result = do
      let parsed = hoistEither (parse stlcInterpreter)
      suspend (mapStateT (pure . runIdentity)) (runChecker (parsed >>= infer emptyContext))
    showReport
      :: CouldBe e ()
      => Reportable r
      => r
      -> ExceptT (Variant e) (StateT CheckState IO) a
    showReport r =
      let diagnostic = addFile def "<test-file>" stlcInterpreter
          diagnostic' = addReport diagnostic (report r)
       in do
            lift (printDiagnostic stdout True True 4 defaultStyle diagnostic')
            throw ()
