module Naive where

import Control.Monad.Except
import NaiveTypeChecker
import Syntax

tm0 :: Term Name
tm0 =
  Let
    "add"
    (Pi Relevant "_" Nat (Pi Relevant "_" Nat Nat))
    ( Lambda
        "m"
        Nat
        ( Lambda
            "n"
            Nat
            (NElim (Lambda "_" Nat Nat) (Var "n") (Lambda "_" Nat (Lambda "k" Nat (Succ (Var "k")))) (Var "m"))
        )
    )
    (App (App (Var "add") (Succ Zero)) (Succ (Succ Zero)))

tm1 :: Term Name
tm1 =
  NElim (Lambda "_" Nat Nat) Zero (Lambda "k" Nat (Lambda "_" Nat (Var "k"))) (Succ Zero)

tm2 :: Term Name
tm2 =
  Let
    "f"
    (Pi Relevant "_" Nat Nat)
    (Lambda "x" Nat (Succ (Var "x")))
    ( Let
        "x"
        Nat
        (Succ (Succ Zero))
        (App (Var "f") (Var "x"))
    )

test :: Term Name -> IO ()
test t =
  case runExcept (infer emptyContext t) of
    Right (t, _, tty) -> do
      putStrLn "Program:"
      putStrLn (prettyPrintTerm t)
      putStrLn "\nReduces to:"
      putStrLn (prettyPrintTerm (eval t))
      putStrLn "\nType:"
      putStrLn (prettyPrintTerm tty)
    Left e -> putStrLn e
