module Naive where

import Syntax
import NaiveTypeChecker

import Control.Monad.Except

tm0 :: Term Name
tm0 =
  Let
  "add"
  (Pi Relevant "_" Nat (Pi Relevant "_" Nat Nat))
  (Lambda "m" Nat
   (Lambda "n" Nat
    (NElim (Lambda "_" Nat Nat) (Var "n") (Lambda "_" Nat (Lambda "k" Nat (Succ (Var "k")))) (Var "m"))))
  (App (App (Var "add") Zero) Zero)

tm1 :: Term Name
tm1 =
  NElim (Lambda "_" Nat Nat) Zero (Lambda "k" Nat (Lambda "_" Nat (Var "k"))) (Succ Zero)

test :: Term Name -> IO ()
test t =
  case runExcept (infer emptyContext t) of
    Right (t, _, tty) -> do
      putStrLn "Program:"
      putStrLn (prettyPrintTerm t)
      putStrLn "\nReduces to:"
      putStrLn (prettyPrintTerm (eval [] t))
      putStrLn "\nType:"
      putStrLn (prettyPrintTerm tty)
    Left e -> putStrLn e
