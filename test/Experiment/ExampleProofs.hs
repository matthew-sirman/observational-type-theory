{-# LANGUAGE QuasiQuotes #-}

module Experiment.ExampleProofs where

import Experiment.TestExecution

import Text.RawString.QQ

boolAsQuotient :: String
boolAsQuotient =
  [r|
    let cast_compose : (A :U U) -> (B :U U) -> (C :U U)
                    -> (AB :Ω A ~ B) -> (BC :Ω B ~ C) -> (AC :Ω A ~ C)
                    -> (x :U A)
                    -> cast(A, C, AC, x) ~ cast(B, C, BC, cast(A, B, AB, x)) =
      λA. λB. λC. λAB. λBC. λAC. λx.
        transp(B, B' BB'. cast(A, B', trans(_, _, _, AB, BB'), x) ~[B'] cast(B, B', BB', cast(A, B, AB, x)),
               castrefl(B, cast(A, B, AB, x)), C, BC)
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
                            λ_. castrefl(B true, t),
                            l _. λw. ⊥-elim(presTRhs 0 (S l) w, w),
                            y),
                      k _.
                        rec(y'. presT (S k) y',
                            λw. ⊥-elim(presTRhs (S k) 0 w, w),
                            l _. λ_. cast_compose (B false) (B (π (S l))) (B (π (S k)))
                                                        (congB (S 0) (S l) *)
                                                        (congB (S l) (S k) *)
                                                        (congB (S 0) (S k) *)
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

stlcInterpreter :: String
stlcInterpreter =
  [r|
    let Ix : ℕ → U =
      μIx : ℕ → U. λn. ['Ix0 : Σ(m : ℕ). [S m ~ n]; 'IxS : Σ(m : ℕ). [S m ~ n] × Ix m]
    in
    let Lvl : U =
      μ_ : U. λ. ['Lvl : ℕ]
    in
    let Term : ℕ → U =
      μTm : ℕ → U. λn. [ 'Var : Ix n
                       ; 'One : [⊤]
                       ; 'Pair : Tm n × Tm n
                       ; 'Fst : Tm n
                       ; 'Snd : Tm n
                       ; 'Lambda : Tm n
                       ; 'App : Tm n × Tm n
                       ]
    in
    let Type : U =
      μTy : U. λ. [ 'Unit : [⊤]
                  ; 'Product : Ty × Ty
                  ; 'Function : Ty × Ty
                  ]
    in
    let Vec : U → ℕ → U =
      λA. μVec : ℕ → U. λn. ['Nil : [n ~ 0]; 'Cons : Σ(m : ℕ). [S m ~ n] × (A × Vec m)]
    in
    let Form : U =
      μ_ : U. λ. ['Ne : [⊤]; 'Nf : [⊤]]
    in
    let Val : Form → U =
      μVal : Form → U. λf. [ 'VVar : [f ~[Form] 'Ne <*>] × Lvl
                           ; 'VOne : [f ~[Form] 'Nf <*>] × [⊤]
                           ; 'VPair : [f ~[Form] 'Nf <*>] × (Val ('Nf <*>) × Val ('Nf <*>))
                           ; 'VFst : [f ~[Form] 'Ne <*>] × Val ('Ne <*>)
                           ; 'VSnd : [f ~[Form] 'Ne <*>] × Val ('Ne <*>)
                           ; 'VLambda : [f ~[Form] 'Nf <*>] × (Σ(m : ℕ). Vec (Val ('Nf <*>)) m × Term (S m))
                           ; 'VApp : [f ~[Form] 'Ne <*>] × (Val ('Ne <*>) × Val ('Nf <*>))
                           ; 'VNe : [f ~[Form] 'Nf <*>] × Val ('Ne <*>)
                           ]
    in
    let Env : ℕ → U = Vec (Val ('Nf <*>)) in
    let lookup : (n :_ ℕ) → Env n → Ix n → Val ('Nf <*>) =
      λn. fix [Env as E] lookup m env : Ix m → Val ('Nf <*>) =
        match env as _ return Ix m → Val ('Nf <*>) with
          | 'Nil m_eq_0 →
            λix.
              (match ix as _ return Val ('Nf <*>) with
                | 'Ix0 s_k_eq_m →
                  let k : ℕ = fst s_k_eq_m in
                  let s_k_eq_m : S k ~ m = ▢-elim(snd s_k_eq_m) in
                  abort(Val ('Nf <*>), trans(S k, m, 0, s_k_eq_m, ▢-elim(m_eq_0)))
                | 'IxS s_k_eq_m →
                  let k : ℕ = fst s_k_eq_m in
                  let s_k_eq_m : S k ~ m = ▢-elim (fst (snd (s_k_eq_m))) in
                  abort(Val ('Nf <*>), trans(S k, m, 0, s_k_eq_m, ▢-elim(m_eq_0)))
              )
          | 'Cons ls →
            let k : ℕ = fst ls in
            let s_k_eq_m : S k ~ m = ▢-elim(fst (snd ls)) in
            let a : Val ('Nf <*>) = fst (snd (snd ls)) in
            let tl : E k = snd (snd (snd ls)) in
            λix.
              (match ix as _ return Val ('Nf <*>) with
                | 'Ix0 _ → a
                | 'IxS ix' →
                  let l : ℕ = fst ix' in
                  let s_l_eq_m = fst (snd ix') in
                  let ix' : Ix l = snd (snd ix') in
                  lookup k tl ix'
              )
    in
    -- let eval : (n :_ ℕ) → Term n → Env n → Val ('Nf <*>) =
    --   fix [Term as Tm] eval tm : Env → Val ('Nf <*>) =
    --     match tm as _ return Env → Val ('Nf <*>) with
    --       | '
    -- in
    *
  |]

_ = test
