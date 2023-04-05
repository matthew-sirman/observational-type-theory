{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeApplications #-}

module Experiment.TestExecution where

import Error
import Parser.Parser
import Syntax
import TypeChecker

import Control.Monad.Except
import Control.Monad.State
import Data.Function ((&))
import Data.Functor.Identity

import Control.Monad.Oops
import Error.Diagnose

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
