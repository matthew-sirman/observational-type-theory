{-# LANGUAGE QuasiQuotes #-}
module NbE where

import Control.Monad.Except

import Text.RawString.QQ
import Test.HUnit

import Parser.Parser
import Syntax
import TypeChecker

programTypeChecks :: String -> String -> VTy Ix -> Assertion
programTypeChecks name source t =
  let result = do
        syntax <- parse source
        runExcept (check emptyContext syntax t)
      isRight (Right _) = True
      isRight (Left _) = False
  in assertBool name (isRight result)

typeUniverse :: Test
typeUniverse = TestList
  [ TestCase (programTypeChecks "Relevant universe has type [U]" termRelevant (VU Relevant))
  , TestCase (programTypeChecks "Irrelevant universe has type [U]" termIrrelevant (VU Relevant))
  ]
  where
    termRelevant :: String
    termRelevant =
      [r|
        U
      |]

    termIrrelevant :: String
    termIrrelevant =
      [r|
        Ω
      |]
