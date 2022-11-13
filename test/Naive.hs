{-# LANGUAGE QuasiQuotes #-}
module Naive where

import Parser.Parser
import Syntax
import NaiveTypeChecker

import Text.RawString.QQ
import Control.Monad.Except

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
    let add : (_ :U Nat) -> (_ :U Nat) -> Nat =
      \(m : Nat). \(n : Nat). rec(\(_ : Nat). Nat, n, \(_ : Nat). \(k : Nat). S k, m)
    in
    add 0 0
  |]

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

test :: String -> IO ()
test input =
  case parse input >>= runExcept . infer emptyContext . eraseSourceLocations of
    Right (t, _, tty) -> do
      putStrLn "Program:"
      putStrLn (prettyPrintTerm t)
      putStrLn "\nReduces to:"
      putStrLn (prettyPrintTerm (eval t))
      putStrLn "\nType:"
      putStrLn (prettyPrintTerm tty)
    Left e -> putStrLn e
