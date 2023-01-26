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
        -- p
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
    λ(A : U). λ(p : S 0 ~[ℕ] 0). abort(A, p)
  |]
leftMap :: (a -> b) -> Either a c -> Either b c
leftMap f (Left a) = Left (f a)
leftMap _ (Right b) = Right b

test :: String -> IO ()
test input =
  -- let result = do
  --       syntax <- parse input
  --       runExcept (infer emptyContext syntax)
  -- in
  let (Right syntax) = parse input in
  case runExcept (infer emptyContext syntax) of
    Right (t, _, tty) -> do
      putStrLn "Program:"
      putStrLn (prettyPrintTerm [] t)
      putStrLn "\nHas type:"
      putStrLn (prettyPrintTerm [] (quote 0 tty))
      putStrLn "\nReduces to:"
      putStrLn (prettyPrintTerm [] (normalForm [] t))
    Left e ->
      let diagnostic = addFile def "<test-file>" input
          diagnostic' = addReport diagnostic e
      in printDiagnostic stdout True True 4 defaultStyle diagnostic'
