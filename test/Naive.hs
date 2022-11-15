{-# LANGUAGE QuasiQuotes #-}
module Naive where

import Parser.Parser
import Syntax
import NaiveTypeChecker

import Text.RawString.QQ
import Control.Monad.Except
import Control.Monad.State

tm0 :: String
tm0 =
  [r|
    let add : (_ :U ℕ) -> (_ :U ℕ) -> ℕ =
      \(m : ℕ). \(n : ℕ). rec(\(_ : ℕ). ℕ, n, \(_ : ℕ). \(k : ℕ). S k, m)
    in
    add (S (S 0)) (S (S (S (S 0))))
  |]

tm1 :: String
tm1 =
  [r|
    rec(\(_ : ℕ). ℕ, 0, \(k : ℕ). \(_ : ℕ). k, S (S (S 0)))
  |]

tm2 :: String
tm2 =
  [r|
    let f : (_ :U ℕ) -> ℕ=
      \(x : ℕ). S x
    in
    let x : ℕ= S (S 0)
    in
    f x
  |]

tm3 :: String
tm3 =
  [r|
    let peano1 : (n :U ℕ) -> (_ :Ω S n ~[ℕ] 0) -> ⊥ =
      λ(n : ℕ). λ(p : S n ~[ℕ] 0).
        transp(S n, λ(x : ℕ). λ(_ : S n ~[ℕ] x). rec(λ(_ : ℕ). Ω, ⊥, λ(_ : ℕ). λ(_ : Ω). ⊤, x), *, 0, p)
    in
    peano1
  |]

tm4 :: String
tm4 =
  [r|
    let peano2 : (x :U ℕ) -> (y :U ℕ) -> (_ :Ω S x ~[ℕ] S y) -> x ~[ℕ] y =
      let pred : (_ :U ℕ) -> ℕ =
        λ(n : ℕ). rec(λ(_ : ℕ). ℕ, 0, λ(k : ℕ). λ(_ : ℕ). k, n)
      in
      λ(x : ℕ). λ(y : ℕ). λ(p : S x ~[ℕ] S y).
        -- transp(S x, λ(n : ℕ). λ(_ : n ~[ℕ] S x). pred n)
        p
    in
    peano2
  |]

tm5 :: String
tm5 =
  [r|
    λ(A : U). λ(p : S 0 ~[ℕ] 0). abort(A, p)
  |]

leftMap :: (a -> b) -> Either a c -> Either b c
leftMap f (Left a) = Left (f a)
leftMap _ (Right b) = Right b

printFailTrace :: [CheckerTrace] -> IO ()
printFailTrace [] = pure ()
printFailTrace (Complete tid : trace) = printFailTrace (filter (not . completes tid) trace)
  where
    completes :: Int -> CheckerTrace -> Bool
    completes tid (Check _ _ _ i) = tid == i
    completes tid (Infer _ _ i) = tid == i
    completes tid (Conv _ _ _ i) = tid == i
    completes _ _ = False
printFailTrace (t : trace) = do
  print t
  printFailTrace trace

showError :: Bool -> (String, [CheckerTrace]) -> IO ()
showError withTrace (e, trace) = do
  putStrLn e
  when withTrace (printFailTrace trace)

test :: String -> IO ()
test input =
  let result = do
        syntax <- leftMap putStrLn (parse input)
        leftMap (showError True) (runExcept (evalStateT (infer emptyContext (eraseSourceLocations syntax)) ([], 0)))
  in
  case result of
    Right (t, _, tty) -> do
      putStrLn "Program:"
      putStrLn (prettyPrintTerm [] t)
      putStrLn "\nReduces to:"
      putStrLn (prettyPrintTerm [] (eval t))
      putStrLn "\nType:"
      putStrLn (prettyPrintTerm [] (eval tty))
    Left errorAction -> errorAction
