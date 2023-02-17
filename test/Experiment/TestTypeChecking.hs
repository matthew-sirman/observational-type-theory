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
    let ap : (A :U U) -> (B :U U) -> (x :U A) -> (y :U A) -> (f :U (z :U A) -> B) -> (_ :Ω x ~[A] y) -> f x ~[B] f y =
      λA. λB. λx. λy. λf. λp.
        transp(x, t _. f x ~[B] f t, refl (f x), y, p)
    in
    ap
  |]

tm5 :: String
tm5 =
  [r|
    let ap : (A :U U) -> (B :U U) -> (x :U A) -> (y :U A) -> (f :U (z :U A) -> B) -> (_ :Ω x ~[A] y) -> f x ~[B] f y =
      λA. λB. λx. λy. λf. λp.
        transp(x, t _. f x ~[B] f t, refl (f x), y, p)
    in

    let peano2 : (x :U ℕ) -> (y :U ℕ) -> (_ :Ω S x ~[ℕ] S y) -> x ~[ℕ] y =
      let pred : (_ :U ℕ) -> ℕ =
        λn. rec(_. ℕ, 0, k _. k, n)
      in
      λx. λy. λp.
        -- transp(S x, n e. ap ℕ ℕ (S x) n pred e, refl x, S y, p)
        ap ℕ ℕ (S x) (S y) pred p
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
    let sym : (A :U U) -> (t :U A) -> (u :U A) -> (_ :Ω t ~[A] u) -> u ~[A] t =
      λA. λt. λu. λp. transp(t, x _. x ~[A] t, refl t, u, p)
    in
    let trans : (A :U U) -> (x :U A) -> (y :U A) -> (z :U A) -> (_ :Ω x ~[A] y) -> (_ :Ω y ~[A] z) -> x ~[A] z =
      λA. λx. λy. λz. λxy. λyz. transp(x, y' _. (_ :Ω y' ~[A] z) -> x ~[A] z, λw. w, y, xy) yz
    in
    let cong : (A :U U) -> (B :U U) -> (x :U A) -> (y :U A) -> (f :U (_ :U A) -> B) -> (_ :Ω x ~[A] y) -> f x ~[B] f y =
      λA. λB. λx. λy. λf. λp. transp(x, n _. f x ~[B] f n, refl (f x), y, p)
    in
    let left_unit : (n :U ℕ) -> add 0 n ~[ℕ] n =
      λn. refl n
    in
    let right_unit : (n :U ℕ) -> add n 0 ~[ℕ] n =
      λn. rec(z. add z 0 ~[ℕ] z, refl 0, k pf. cong ℕ ℕ (add k 0) k (λm. S m) pf, n)
    in
    let succ_comm_right : (n :U ℕ) -> (m :U ℕ) -> add n (S m) ~[ℕ] S (add n m) =
      λn. λm. rec(k. add k (S m) ~[ℕ] S (add k m),
                  refl (S m),
                  k ih. cong ℕ ℕ (add k (S m)) (S (add k m)) (λx. S x) ih,
                  n)
    in
    let add_comm : (n :U ℕ) -> (m :U ℕ) -> add n m ~[ℕ] add m n =
      λn. λm.
        rec(k. add n k ~[ℕ] add k n,
            right_unit n,
            k ih.
              let ap_succ : S (add n k) ~[ℕ] S (add k n) = cong ℕ ℕ (add n k) (add k n) (λx. S x) ih in
              trans ℕ (add n (S k)) (S (add n k)) (add (S k) n) (succ_comm_right n k) ap_succ,
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
    let ap : (A :U U) -> (B :U U)
          -> (x :U A) -> (y :U A)
          -> (f :U (z :U A) -> B)
          -> (_ :Ω x ~[A] y) -> f x ~[B] f y =
      λA. λB. λx. λy. λf. λp.
        transp(x, t _. f x ~[B] f t, refl (f x), y, p)
    in
    let eq_trans : (A :U U)
                -> (x :U A) -> (y :U A) -> (z :U A)
                -> (xy :Ω x ~[A] y) -> (yz :Ω y ~[A] z)
                -> x ~[A] z =
      λA. λx. λy. λz. λxy. transp(x, y' _. (_ :Ω y' ~[A] z) -> x ~[A] z, λw. w, y, xy)
    in
    let cast_compose : (A :U U) -> (B :U U) -> (C :U U)
                    -> (AB :Ω A ~[U] B) -> (BC :Ω B ~[U] C) -> (AC :Ω A ~[U] C)
                    -> (x :U A)
                    -> cast(A, C, AC, x) ~[C] cast(B, C, BC, cast(A, B, AB, x)) =
      λA. λB. λC. λAB. λBC. λAC. λx.
        transp(B, B' BB'. cast(A, B', eq_trans U A B B' AB BB', x) ~[B'] cast(B, B', BB', cast(A, B, AB, x)),
               castrefl(B, cast(A, B, AB, x)), C, BC)
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
          λx. λy. λxRy. ap Bool U (π x) (π y) B xRy
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

tm17 :: String
tm17 =
  [r|
    let ap : (A :U U) -> (B :U U)
          -> (x :U A) -> (y :U A)
          -> (f :U (z :U A) -> B)
          -> (_ :Ω x ~[A] y) -> f x ~[B] f y =
      λA. λB. λx. λy. λf. λp.
        transp(x, t _. f x ~[B] f t, refl (f x), y, p)
    in
    let eq_trans : (A :U U)
                -> (x :U A) -> (y :U A) -> (z :U A)
                -> (xy :Ω x ~[A] y) -> (yz :Ω y ~[A] z)
                -> x ~[A] z =
      λA. λx. λy. λz. λxy. transp(x, y' _. (_ :Ω y' ~[A] z) -> x ~[A] z, λw. w, y, xy)
    in
    let cast_compose : (A :U U) -> (B :U U) -> (C :U U)
                    -> (AB :Ω A ~[U] B) -> (BC :Ω B ~[U] C) -> (AC :Ω A ~[U] C)
                    -> (x :U A)
                    -> cast(A, C, AC, x) ~[C] cast(B, C, BC, cast(A, B, AB, x)) =
      λA. λB. λC. λAB. λBC. λAC. λx.
        transp(B, B' BB'. cast(A, B', eq_trans U A B B' AB BB', x) ~[B'] cast(B, B', BB', cast(A, B, AB, x)),
               castrefl(B, cast(A, B, AB, x)), C, BC)
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
          λx. λy. λxRy. ap Bool U (π x) (π y) B xRy
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
    id2 ℕ 0
  |]

tm20 :: String
tm20 =
  [r|
    let sym : (A :U U) -> (x :U A) -> (y :U A) -> (_ :Ω x ~[_] y) -> y ~[_] x =
      λA. λx. λy. λpf. transp(x, z _. z ~[A] x, refl x, y, pf)
    in
    (λn. sym ℕ n n (refl n) : (n :U ℕ) -> n ~[ℕ] n)
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
      putStrLn (prettyPrintTerm [] (quote 0 tty))
      putStrLn "\nReduces to:"
      putStrLn (prettyPrintTerm [] (normalForm [] t))
      putStrLn "\nMeta context:"
      print mctx
    Left () -> pure ()
  where
    result = do
      let parsed = hoistEither (parse input)
      suspend (mapStateT (pure . runIdentity)) (parsed >>= infer emptyContext)
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
