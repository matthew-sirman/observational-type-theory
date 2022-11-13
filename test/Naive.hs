{-# LANGUAGE QuasiQuotes #-}
module Naive where

import Parser.Parser
import Syntax
import NaiveTypeChecker

import Text.RawString.QQ
import Control.Monad.Except
import Control.Monad.State

-- tm0 :: Term Name
-- tm0 =
--   Let
--   "add"
--   (Pi Relevant "_" Nat (Pi Relevant "_" Nat Nat))
--   (Lambda "m" Nat
--    (Lambda "n" Nat
--     (NElim (Lambda "_" Nat Nat) (Var "n") (Lambda "_" Nat (Lambda "k" Nat (Succ (Var "k")))) (Var "m"))))
--   (App (App (Var "add") Zero) Zero)

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
      \(n : ℕ). \(p : S n ~[ℕ] 0).
        transp(S n, \(x : ℕ). \(_ : S n ~[ℕ] x). rec(\(_ : ℕ). Ω, ⊥, \(_ : ℕ). \(_ : Ω). ⊤, x), *, 0, p)
    in
    peano1
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
