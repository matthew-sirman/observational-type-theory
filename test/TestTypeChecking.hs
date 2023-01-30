{-# LANGUAGE QuasiQuotes #-}
module TestTypeChecking where

import Parser.Parser
import Syntax
import TypeChecker

import Text.RawString.QQ
import Control.Monad.Except

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
    let succ_comm_left : (n :U ℕ) -> (m :U ℕ) -> add n (S m) ~[ℕ] S (add n m) =
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
              trans ℕ (add n (S k)) (S (add n k)) (add (S k) n) (succ_comm_left n k) ap_succ,
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

test :: String -> IO ()
test input =
  -- let result = do
  --       syntax <- parse input
  --       runExcept (infer emptyContext syntax)
  -- in
  let result = do
        syntax <- parse input
        runExcept (infer emptyContext syntax)
  in
  case result of
    Left e ->
      let diagnostic = addFile def "<test-file>" input
          diagnostic' = addReport diagnostic e
      in printDiagnostic stdout True True 4 defaultStyle diagnostic'
    Right (t, _, tty) -> do
      putStrLn "Program:"
      putStrLn (prettyPrintTerm [] t)
      putStrLn "\nHas type:"
      putStrLn (prettyPrintTerm [] (quote 0 tty))
      putStrLn "\nReduces to:"
      putStrLn (prettyPrintTerm [] (normalForm [] t))
