{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}

module Experiment.TestTypeChecking where

import Error
import Parser.Parser
import Syntax
import TypeChecker

import Control.Monad.Except
import Control.Monad.State
import Data.Function ((&))
import Data.Functor.Identity
import Text.RawString.QQ

import Control.Monad.Oops
import Error.Diagnose

tm0 :: String
tm0 =
  [r|
    let add : (_ :U ℕ) -> (_ :U ℕ) -> ℕ =
      \m. \n. rec(_ . ℕ, n, _ k. S k, m)
    in
    add (S (S 0)) (S (S (S (S 0))))
  |]

tm1 :: String
tm1 =
  [r|
    rec(_. ℕ, 0, k _. k, S (S (S 0)))
  |]

tm2 :: String
tm2 =
  [r|
    let f : (_ :U ℕ) -> ℕ =
      \x. S x
    in
    let x : ℕ =
      S (S 0)
    in
    f x
  |]

tm3 :: String
tm3 =
  [r|
    let peano1 : (n :U ℕ) -> (_ :Ω S n ~[ℕ] 0) -> ⊥ =
      λn. λp.
        transp(S n, x _. rec(_. Ω, ⊥, _ _. ⊤, x), *, 0, p)
    in
    peano1
  |]

tm4 :: String
tm4 =
  [r|
    -- let ap : (A :U U) -> (B :U U) -> (x :U A) -> (y :U A) -> (f :U (z :U A) -> B) -> (_ :Ω x ~[A] y) -> f x ~[B] f y =
    --   λA. λB. λx. λy. λf. λp.
    --     transp(x, t _. f x ~[B] f t, refl (f x), y, p)
    -- in
    ap(_, x. 0, 0, 0, refl 0)
  |]

tm5 :: String
tm5 =
  [r|
    -- let ap : (A :U U) -> (B :U U) -> (x :U A) -> (y :U A) -> (f :U (z :U A) -> B) -> (_ :Ω x ~[A] y) -> f x ~[B] f y =
    --   λA. λB. λx. λy. λf. λp.
    --     transp(x, t _. f x ~[B] f t, refl (f x), y, p)
    -- in

    let peano2 : (x :U ℕ) -> (y :U ℕ) -> (_ :Ω S x ~[ℕ] S y) -> x ~[ℕ] y =
      -- let pred : (_ :U ℕ) -> ℕ =
      --   λn. rec(_. ℕ, 0, k _. k, n)
      -- in
      λx. λy. λp.
        -- transp(S x, n e. ap ℕ ℕ (S x) n pred e, refl x, S y, p)
        ap(ℕ, n. rec(_. ℕ, 0, k _. k, n), S x, S y, p)
        -- p
    in
    peano2
  |]

tm6 :: String
tm6 =
  [r|
    let t : (A :U U) -> (_ :Ω ⊥) -> A =
      λA. λp. abort(A, p)
    in
    t
  |]

tm7 :: String
tm7 =
  [r|
    (* : ⊤)
  |]

tm8 :: String
tm8 =
  [r|
    (λA. A : (_ :U ℕ) -> ℕ)
  |]

tm9 :: String
tm9 =
  [r|
    let add : (_ :U ℕ) -> (_ :U ℕ) -> ℕ =
      λn. λm. rec(_. ℕ, m, _ k. S k, n)
    in
    -- let sym : (A :U U) -> (t :U A) -> (u :U A) -> (_ :Ω t ~[A] u) -> u ~[A] t =
    --   λA. λt. λu. λp. transp(t, x _. x ~[A] t, refl t, u, p)
    -- in
    -- let trans : (A :U U) -> (x :U A) -> (y :U A) -> (z :U A) -> (_ :Ω x ~[A] y) -> (_ :Ω y ~[A] z) -> x ~[A] z =
    --   λA. λx. λy. λz. λxy. λyz. transp(x, y' _. (_ :Ω y' ~[A] z) -> x ~[A] z, λw. w, y, xy) yz
    -- in
    -- let cong : (A :U U) -> (B :U U) -> (x :U A) -> (y :U A) -> (f :U (_ :U A) -> B) -> (_ :Ω x ~[A] y) -> f x ~[B] f y =
    --   λA. λB. λx. λy. λf. λp. transp(x, n _. f x ~[B] f n, refl (f x), y, p)
    -- in
    let left_unit : (n :U ℕ) -> add 0 n ~[ℕ] n =
      λn. refl n
    in
    let right_unit : (n :U ℕ) -> add n 0 ~[ℕ] n =
      λn. rec(z. add z 0 ~[ℕ] z, refl 0, k pf. ap(ℕ, m. S m, add k 0, k, pf), n)
    in
    let succ_comm_right : (n :U ℕ) -> (m :U ℕ) -> add n (S m) ~[ℕ] S (add n m) =
      λn. λm. rec(k. add k (S m) ~[ℕ] S (add k m),
                  refl (S m),
                  k ih. ap(ℕ, x. S x, add k (S m), S (add k m), ih),
                  n)
    in
    let add_comm : (n :U ℕ) -> (m :U ℕ) -> add n m ~[ℕ] add m n =
      λn. λm.
        rec(k. add n k ~[ℕ] add k n,
            right_unit n,
            k ih.
              let ap_succ : S (add n k) ~[ℕ] S (add k n) = ap(ℕ, x. S x, add n k, add k n, ih) in
              trans(add n (S k), S (add n k), add (S k) n, succ_comm_right n k, ap_succ),
            m)
    in
    add_comm (S (S 0)) (S 0)
  |]

tm10 :: String
tm10 =
  [r|
    let id : (A :U U) -> (x :U A) -> A =
      λA. λx. x
    in
    refl id
  |]

tm11 :: String
tm11 =
  [r|
    let f : (x :U ℕ) -> ℕ =
      λx. S x
    in
    let g : (x :U ℕ) -> ℕ =
      λx. rec(_. ℕ, 0, k _. k, x)
    in
    let f_neq_g : (_ :Ω f ~[(x :U ℕ) -> ℕ] g) -> ⊥ =
      λpf. pf 0
    in
    *
  |]

tm12 :: String
tm12 =
  [r|
    let succ : (x :U ℕ) -> ℕ =
      λx. S x
    in
    let pred : (x :U ℕ) -> ℕ =
      λx. rec(_. ℕ, 0, k _. k, x)
    in
    let id1 : (x :U ℕ) -> ℕ =
      λx. x
    in
    let id2 : (x :U ℕ) -> ℕ =
      λx. pred (succ x)
    in
    let id3 : (x :U ℕ) -> ℕ =
      λx. succ (pred x)
    in
    let id1_eq_id2 : id1 ~[(x :U ℕ) -> ℕ] id2 =
      λx. refl x
    in
    let id1_neq_id3 : (_ :Ω id1 ~[(x :U ℕ) -> ℕ] id3) -> ⊥  =
      λpf. pf 0
    in
    *
  |]

tm13 :: String
tm13 =
  [r|
    let f : (x :U ℕ) -> ℕ =
      λx. S x
    in
    snd (refl ((x :U ℕ) -> ℕ))
  |]

tm14 :: String
tm14 =
  [r|
    castrefl((x :U ℕ) -> ℕ, λx. x) 0
  |]

tm15 :: String
tm15 =
  [r|
    let R : (_ :U ℕ) -> (_ :U ℕ) -> Ω =
      λx. λy. rec(_. Ω, rec(_. Ω, ⊤, _ _. ⊥, y), _ _. rec(_. Ω, ⊥, _ _. ⊤, y), x)
    in
    let Rr : (x :U ℕ) -> R x x =
      λx. rec(z. R z z, *, _ _. *, x)
    in
    let Rs : (x :U ℕ) -> (y :U ℕ) -> (_ :Ω R x y) -> R y x =
      λx. λy. rec(y'. (_ :Ω R x y') -> R y' x,
                  rec(x'. (_ :Ω R x' 0) -> R 0 x', λw. w, _ _. λw. w, x),
                  k _. rec(x'. (_ :Ω R x' (S k)) -> R (S k) x', λw. w, _ _. λw. w, x),
                  y)
    in
    let Rt : (x :U ℕ) -> (y :U ℕ) -> (z :U ℕ) -> (_ :Ω R x y) -> (_ :Ω R y z) -> R x z =
      λx. λy. λz. rec(z'. (_ :Ω R x y) -> (_ :Ω R y z') -> R x z',
                      rec(y'. (_ :Ω R x y') -> (_ :Ω R y' 0) -> R x 0,
                          λx0. λ_. x0,
                          k _. λ_. λw. ⊥-elim(R x 0, w),
                          y),
                      k _. rec(y'. (_ :Ω R x y') -> (_ :Ω R y' (S k)) -> R x (S k),
                               λ_. λw. ⊥-elim(R x (S k), w),
                               l _. rec(x'. (_ :Ω R x' (S l)) -> (_ :Ω R (S l) (S k)) -> R x' (S k),
                                        λw. λ_. w,
                                        _ _. λ_. λ_. *,
                                        x),
                               y),
                      z)
    in
    *
  |]

tm16 :: String
tm16 =
  [r|
    -- let ap : (A :U U) -> (B :U U)
    --       -> (x :U A) -> (y :U A)
    --       -> (f :U (z :U A) -> B)
    --       -> (_ :Ω x ~[A] y) -> f x ~[B] f y =
    --   λA. λB. λx. λy. λf. λp.
    --     transp(x, t _. f x ~[B] f t, refl (f x), y, p)
    -- in
    -- let eq_trans : (A :U U)
    --             -> (x :U A) -> (y :U A) -> (z :U A)
    --             -> (xy :Ω x ~[A] y) -> (yz :Ω y ~[A] z)
    --             -> x ~[A] z =
    --   λA. λx. λy. λz. λxy. transp(x, y' _. (_ :Ω y' ~[A] z) -> x ~[A] z, λw. w, y, xy)
    -- in
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

    let R : (_ :U ℕ) -> (_ :U ℕ) -> Ω =
      λx. λy. rec(_. Ω, rec(_. Ω, ⊤, _ _. ⊥, y), _ _. rec(_. Ω, ⊥, _ _. ⊤, y), x)
    in
    let Rr : (x :U ℕ) -> R x x =
      λx. rec(z. R z z, *, _ _. *, x)
    in
    let Rs : (x :U ℕ) -> (y :U ℕ)
          -> (_ :Ω R x y) -> R y x =
      λx. λy. rec(y'. (_ :Ω R x y') -> R y' x,
                  rec(x'. (_ :Ω R x' 0) -> R 0 x', λw. w, _ _. λw. w, x),
                  k _. rec(x'. (_ :Ω R x' (S k)) -> R (S k) x', λw. w, _ _. λw. w, x),
                  y)
    in
    let Rt : (x :U ℕ) -> (y :U ℕ) -> (z :U ℕ)
          -> (_ :Ω R x y) -> (_ :Ω R y z) -> R x z =
      λx. λy. λz. rec(z'. (_ :Ω R x y) -> (_ :Ω R y z') -> R x z',
                      rec(y'. (_ :Ω R x y') -> (_ :Ω R y' 0) -> R x 0,
                          λx0. λ_. x0,
                          k _. λ_. λw. ⊥-elim(R x 0, w),
                          y),
                      k _. rec(y'. (_ :Ω R x y') -> (_ :Ω R y' (S k)) -> R x (S k),
                               λ_. λw. ⊥-elim(R x (S k), w),
                               l _. rec(x'. (_ :Ω R x' (S l)) -> (_ :Ω R (S l) (S k)) -> R x' (S k),
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
    let if : (B :U (_ :U Bool) -> U) -> (c :U Bool) -> (_ :U B true) -> (_ :U B false) -> B c =
      λB. λc. λt. λf.
        let congB : (x :U ℕ) -> (y :U ℕ) -> (_ :Ω R x y) -> B (π x) ~[U] B (π y) =
          λx. λy. λxRy. ap(U, x. B x, (π x : Bool), π y, xRy)
        in
        let choose : (x :U ℕ) -> B (π x) =
          λx. rec(x'. B (π x'), t, k _. cast(B false, B (π (S k)),
                                             congB (S 0) (S k) *,
                                             f), x)
        in
        let presTRhs : (x :U ℕ) -> (y :U ℕ) -> (_ :Ω R x y) -> Ω =
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

tm17 :: String
tm17 =
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

    let R : (_ :U ℕ) -> (_ :U ℕ) -> Ω =
      λx. λy. rec(_. Ω, rec(_. Ω, ⊤, _ _. ⊥, y), _ _. rec(_. Ω, ⊥, _ _. ⊤, y), x)
    in
    let Rr : (x :U ℕ) -> R x x =
      λx. rec(z. R z z, *, _ _. *, x)
    in
    let Rs : (x :U ℕ) -> (y :U ℕ)
          -> (_ :Ω R x y) -> R y x =
      λx. λy. rec(y'. (_ :Ω R x y') -> R y' x,
                  rec(x'. (_ :Ω R x' 0) -> R 0 x', λw. w, _ _. λw. w, x),
                  k _. rec(x'. (_ :Ω R x' (S k)) -> R (S k) x', λw. w, _ _. λw. w, x),
                  y)
    in
    let Rt : (x :U ℕ) -> (y :U ℕ) -> (z :U ℕ)
          -> (_ :Ω R x y) -> (_ :Ω R y z) -> R x z =
      λx. λy. λz. rec(z'. (_ :Ω R x y) -> (_ :Ω R y z') -> R x z',
                      rec(y'. (_ :Ω R x y') -> (_ :Ω R y' 0) -> R x 0,
                          λx0. λ_. x0,
                          k _. λ_. λw. ⊥-elim(R x 0, w),
                          y),
                      k _. rec(y'. (_ :Ω R x y') -> (_ :Ω R y' (S k)) -> R x (S k),
                               λ_. λw. ⊥-elim(R x (S k), w),
                               l _. rec(x'. (_ :Ω R x' (S l)) -> (_ :Ω R (S l) (S k)) -> R x' (S k),
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
    let if : (B :U (_ :U Bool) -> U) -> (c :U Bool) -> (_ :U B true) -> (_ :U B false) -> B c =
      λB. λc. λt. λf.
        let congB : (x :U ℕ) -> (y :U ℕ) -> (_ :Ω R x y) -> B (π x) ~[U] B (π y) =
          λx. λy. λxRy. ap(U, x. B x, (π x : Bool), π y, xRy)
        in
        let choose : (x :U ℕ) -> B (π x) =
          λx. rec(x'. B (π x'), t, k _. cast(B false, B (π (S k)),
                                             congB (S 0) (S k) *,
                                             f), x)
        in
        let presTRhs : (x :U ℕ) -> (y :U ℕ) -> (_ :Ω R x y) -> Ω =
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
    let Either : (_ :U U) -> (_ :U U) -> U =
      λA. λB. Σ(t : Bool). (if (λ_. U) t A B)
    in
    let inl : (A :U U) -> (B :U U) -> (x :U A) -> Either A B =
      λ_. λ_. λx. (true; x)
    in
    let inr : (A :U U) -> (B :U U) -> (y :U B) -> Either A B =
      λ_. λ_. λy. (false; y)
    in
    -- let if : (B :U (_ :U Bool) -> U) -> (c :U Bool) -> (_ :U B true) -> (_ :U B false) -> B c =
    let case : (A :U U) -> (B :U U) -> (C :U (_ :U Either A B) -> U)
            -> (e :U Either A B)
            -> (_ :U (x :U A) -> C (inl A B x))
            -> (_ :U (y :U B) -> C (inr A B y))
            -> C e =
      λA. λB. λC. λe. λleft. λright.
        if (λt. (v :U if (λ_. U) t A B) -> C (t; v)) (fst e) left right (snd e)
    in
    case Bool ℕ (λ_. ℕ) (inl Bool ℕ false) (λb. if (λ_. ℕ) b (S (S 0)) (S (S (S 0)))) (λy. rec(_. ℕ, 0, k _. k, y))
  |]

tm18 :: String
tm18 =
  [r|
    let f : (A :U U) -> (t :U A) -> (u :U A) -> (_ :Ω t ~[A] u) -> Id(A, t, u) =
      λA. λt. λu. λe. Idpath e
    in
    let g : (A :U U) -> (t :U A) -> (u :U A) -> (_ :U Id(A, t, u)) -> t ~[A] u =
      λA. λt. λu. λe. J(A, t, x _. t ~[A] x, refl t, u, e)
    in
    let a : (A :U U) -> (t :U A) -> (u :U A)
         -> (λe. f A t u (g A t u e)) ~[(_ :U Id(A, t, u)) -> Id(A, t, u)] (λe. e) =
      λA. λt. λu. λe. *
    in
    *
  |]

tm19 :: String
tm19 =
  [r|
    let id : (A :U U) -> (x :U A) -> A =
      λA. λx. x
    in
    let id2 : (A :U U) -> (x :U A) -> A =
      λA. λx. id _ x
    in
    id2 _ 0
  |]

tm20 :: String
tm20 =
  [r|
    (λn. sym(_, _, refl n) : (n :U ℕ) -> n ~[ℕ] n)
  |]

tm21 :: String
tm21 =
  [r|
    (λn. λm. λpf. pf : (n :U ℕ) -> (m :U ℕ) -> (_ :Ω n ~[ℕ] m) -> m ~[ℕ] n)
  |]

tm22 :: String
tm22 =
  [r|
    (0 : fst (_ : U × _))
  |]

tm23 :: String
tm23 =
  [r|
    (0 : snd (_ : _ × U))
  |]

tm24 :: String
tm24 =
  [r|
    let f : (A :U U) -> A -> A = _
    in f ℕ 0
  |]

tm25 :: String
tm25 =
  [r|
    let pred : ℕ -> ℕ =
      λn.
      match n as _ return ℕ with
        | 0 -> 0
        | S n -> n
    in
    pred (S (S (S (S 0))))
  |]

tm26 :: String
tm26 =
  [r|
    let pred1 : ℕ → ℕ =
      λn. rec(_. ℕ, 0, k _. k, n)
    in
    let pred2 : ℕ → ℕ =
      λn.
      match n as _ return ℕ with
        | 0 -> 0
        | S n -> n
    in
    let pred_eq : pred1 ~ pred2 =
      λn. rec(z. pred1 z ~ pred2 z, refl 0, k _. refl k, n)
    in
    *
  |]

tm27 :: String
tm27 =
  [r|
    (refl (◇ * : ▢ ⊤) : ◇ (refl 0) ~[▢ ⊤] ◇ *)
  |]

tm28 :: String
tm28 =
  [r|
    let Vec : U → ℕ → U =
      λA. λn. rec(_. U, ▢⊤, _ vn. A × vn, n)
    in
    ((0; (0; ◇*)): Vec ℕ (S (S 0)))
  |]

tm29 :: String
tm29 =
  [r|
    let Vec : U → ℕ → U =
      λA. μF : ℕ → U. λn. ['Nil : [n ~ 0] × [⊤]; 'Cons : A × (Σ(m : ℕ). ([n ~ S m] × F m))]
    in
    ('Cons (S (S 0); (0; (<refl (S 0)>; 'Nil (<refl 0>; <*>)))) : Vec ℕ (S 0))
  |]

tm30 :: String
tm30 =
  [r|
    let Vec : U → ℕ → U =
      λA. μF : ℕ → U. λn. ['Nil : [n ~ 0] × [⊤]; 'Cons : A × (Σ(m : ℕ). ([n ~ S m] × F m))]
    in
    let empty : Vec ℕ 0 =
      'Nil (<refl 0>; <*>)
    in
    let ls : Vec ℕ (S 0) =
      'Cons (S (S 0); (0; (<refl (S 0)>; 'Nil (<refl 0>; <*>))))
    in
    match ls as _ return ℕ with
      | 'Cons x -> fst x
      | 'Nil _ -> 0
  |]

tm31 :: String
tm31 =
  [r|
    -- This is possibly a naive translation of inductive equality into a uniform
    -- inductive type, but could possibly be simplified by having ['Refl : [x ~ y]]
    let IEq : (A :U U) → A → A → U =
      λA. μ_ : A → A → U. λx y. ['Refl : Σ(a : A). ([a ~ x] × [a ~ y])]
    in
    -- This implementation of J does not work, as we cannot transport observational
    -- equality into a relevant universe.
    -- let J' : (A :U U) → (C :U (x :U A) → (y :U A) → IEq A x y → U) → (x :U A) → (y :U A)
    --        → (t :U IEq A x y) → ((w :U A) → C w w ('Refl (w; (<refl w>; <refl w>)))) → C x y t =
    --   λA. λC. λx. λy. λt. λf.
    --     match t as t return C x y t with
    --       | 'Refl p ->
    --         let a : A = fst p in
    --         let a_eq_x : a ~ x = ▢-elim(fst (snd p)) in
    --         let a_eq_y : a ~ y = ▢-elim(snd (snd p)) in
    --         let x_eq_y : x ~ y = trans(x, a, y, sym(a, x, a_eq_x), a_eq_y) in
    --         transp(x, z x_eq_z. C x z ('Refl (x; (<refl x>; <x_eq_z>))), f x, y, x_eq_y)
    -- in
    IEq ℕ 0 (S 0)
  |]

tm32 :: String
tm32 =
  [r|
    let Nat' : U =
      μN : U. λ. ['Zero : [⊤]; 'Succ : N]
    in
    (λn. 'Succ n ~[Nat'] 'Succ n : Nat' → Ω)
  |]

tm33 :: String
tm33 =
  [r|
    let Vec : U → ℕ → ℕ → U =
      λA. μF : ℕ → ℕ → U. λn _. ['Nil : [n ~ 0] × [⊤]; 'Cons : A × (Σ(m : ℕ). ([n ~ S m] × F m 0))]
    in
    Vec ℕ 0 (S 0)
  |]

tm34 :: String
tm34 =
  [r|
    let List : U → U =
      λA. μF : U. λ. ['Nil : [⊤]; 'Cons : A × F]
    in
    let generate : (A :U U) → (ℕ → A) → ℕ → List A =
      λA. λf. λn. rec(_. List A, 'Nil <*>, k ls. 'Cons (f k; ls), n)
    in
    let length : (A :U U) → List A → ℕ =
      λA. fix [List A as G] length x : ℕ =
        match x as _ return ℕ with
          | 'Nil _ → 0
          | 'Cons ls →
            let tl : G = snd ls in
            S (length tl)
    in
    let map : (A :U U) → (B :U U) → (A → B) → List A → List B =
      λA. λB. λf. fix [List A as G] mapf x : List B =
        match x as _ return List B with
          | 'Nil _ → 'Nil <*>
          | 'Cons ls →
            let a : A = fst ls in
            let tl : G = snd ls in
            'Cons (f a; mapf tl)
    in
    let foldr : (A :U U) → (B :U U) → B → (A → B → B) → List A → B =
      λA. λB. λnil. λcons. fix [List A as G] fold x : B =
        match x as _ return B with
          | 'Nil _ → nil
          | 'Cons ls →
            let a : A = fst ls in
            let tl : G = snd ls in
            cons a (fold tl)
    in
    let ls : List ℕ =
      generate _ (λ_. 0) (S (S 0))
    in
    -- length _ ls
    -- map _ _ (λx. S x) ls
    foldr _ _ 0 (λ_. λn. S n) ls
  |]

tm35 :: String
tm35 =
  [r|
    let Vec : U → ℕ → U =
       λA. μF : ℕ → U. λn. ['Nil : [n ~ 0]; 'Cons : A × (Σ(m : ℕ). ([n ~ S m] × F m))]
    in
    let generate : (A :U U) → (ℕ → A) → (n :U ℕ) → Vec A n =
      λA. λf. λn. rec(k. Vec A k, 'Nil <refl 0>, k vs. 'Cons (f k; (k; (<refl (S k)>; vs))), n)
    in
    let map : (A :U U) → (B :U U) → (A → B) → (n :U ℕ) → Vec A n → Vec B n =
      λA. λB. λf. fix [Vec A as G] mapf n x : Vec B n =
        match x as _ return Vec B n with
          | 'Nil pf → 'Nil pf
          | 'Cons ls →
            let a : A = fst ls in
            let m : ℕ = fst (snd ls) in
            let pf : [n ~ S m] = fst (snd (snd ls)) in
            let tl : G m = snd (snd (snd ls)) in
            'Cons (f a; (m; (pf; mapf m tl)))
    in
    let foldr : (A :U U) → (B :U U) → B → (A → B → B) → (n :U ℕ) → Vec A n → B =
      λA. λB. λnil. λcons. fix [Vec A as G] fold n x : B =
        match x as _ return B with
          | 'Nil _ → nil
          | 'Cons ls →
            let a : A = fst ls in
            let m : ℕ = fst (snd ls) in
            let tl : G m = snd (snd (snd ls)) in
            cons a (fold m tl)
    in
    -- map _ [⊤] (λx. <*>) _ (generate _ (λn. n) (S (S 0)))
    foldr _ _ 0 (λ_. λn. S n) _ (generate _ (λn. n) (S (S (S 0))))
  |]

test :: String -> IO ()
test input = do
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
      emptyMetaContext
  case result of
    Right (t, tty, _) -> do
      putStrLn "Program:"
      putStrLn (prettyPrintTerm [] t)
      putStrLn "\nHas type:"
      putStrLn (prettyPrintTerm [] (runEvaluator (quote 0 tty) mctx))
      putStrLn "\nReduces to:"
      putStrLn (prettyPrintTerm [] (runEvaluator (normalForm [] t) mctx))
      putStrLn "\nMeta context:"
      print mctx
    Left () -> do
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
      -> ExceptT (Variant e) (StateT MetaContext IO) a
    showReport r =
      let diagnostic = addFile def "<test-file>" input
          diagnostic' = addReport diagnostic (report r)
       in do
            lift (printDiagnostic stdout True True 4 defaultStyle diagnostic')
            throw ()
