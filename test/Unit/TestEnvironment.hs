{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Unit.TestEnvironment where

import Control.Monad.Except

import Test.HUnit

import Control.Monad.Oops
import Data.Function ((&))
import Data.Functor.Identity (runIdentity)

import Error
import Parser.Parser
import Syntax
import TypeChecker

type TestChecker result
   = forall e. ( CouldBe e ParseError
               , CouldBe e ConversionError
               , CouldBe e CheckError
               , CouldBe e InferenceError
               ) =>
                 Raw -> Checker (Variant e) result

runTest ::
     TestChecker result
  -> (result -> Assertion)
  -> (ParseError -> Assertion)
  -> (ConversionError -> Assertion)
  -> (CheckError -> Assertion)
  -> (InferenceError -> Assertion)
  -> String
  -> Assertion
runTest checker successHandler parseEHandler convEHandler checkEHandler inferEHandler input = do
  result <-
    runOopsInEither
      (result & catch @ParseError (liftEHandler parseEHandler) &
       catch @ConversionError (liftEHandler convEHandler) &
       catch @CheckError (liftEHandler checkEHandler) &
       catch @InferenceError (liftEHandler inferEHandler))
  case result of
    Right result -> successHandler result
    Left () -> pure ()
  where
    result = do
      let parsed = hoistEither (parse input)
      suspend (pure . runIdentity) (parsed >>= checker)
    liftEHandler ::
         CouldBe err () => (e -> Assertion) -> e -> ExceptT (Variant err) IO a
    liftEHandler h a = lift (h a) >> throw ()

runTestIgnoreErrors ::
     TestChecker result
  -> (result -> Assertion)
  -> Assertion
  -> String
  -> Assertion
runTestIgnoreErrors checker success failure =
  runTest
    checker
    success
    (const failure)
    (const failure)
    (const failure)
    (const failure)

runTestIgnoreData ::
     TestChecker result -> Assertion -> Assertion -> String -> Assertion
runTestIgnoreData checker success = runTestIgnoreErrors checker (const success)

checkClosedType ::
     (CouldBe e ConversionError, CouldBe e CheckError, CouldBe e InferenceError)
  => Raw
  -> Checker (Variant e) (Term Ix, Relevance)
checkClosedType = checkType emptyContext

checkClosed ::
     (CouldBe e ConversionError, CouldBe e CheckError, CouldBe e InferenceError)
  => VTy Ix
  -> Raw
  -> Checker (Variant e) (Term Ix)
checkClosed t raw = check emptyContext raw t

inferClosed ::
     (CouldBe e ConversionError, CouldBe e CheckError, CouldBe e InferenceError)
  => Raw
  -> Checker (Variant e) (Term Ix, VTy Ix, Relevance)
inferClosed = infer emptyContext

passed, failed :: Assertion
passed = assertBool "" True

failed = assertBool "" False

programTypeChecks :: String -> String -> Test
programTypeChecks source =
  let checkTerm vty = runTestIgnoreData (checkClosed vty) passed failed
   in TestCase .
      runTestIgnoreErrors
        checkClosedType
        (\(ty, _) -> checkTerm (eval [] ty) source)
        failed

class FailsWith t where
  testFailsWith ::
       forall result.
       (t -> Assertion)
    -> TestChecker result
    -> String
    -> Assertion

instance FailsWith ParseError where
  testFailsWith parse checker =
    runTest
      checker
      (const failed)
      parse
      (const failed)
      (const failed)
      (const failed)

instance FailsWith ConversionError where
  testFailsWith conversion checker =
    runTest
      checker
      (const failed)
      (const failed)
      conversion
      (const failed)
      (const failed)

instance FailsWith CheckError where
  testFailsWith check checker =
    runTest
      checker
      (const failed)
      (const failed)
      (const failed)
      check
      (const failed)

instance FailsWith InferenceError where
  testFailsWith infer checker =
    runTest
      checker
      (const failed)
      (const failed)
      (const failed)
      (const failed)
      infer

programFailsWith ::
     forall x. FailsWith x
  => String
  -> String
  -> Test
programFailsWith source =
  let checkTerm vty = testFailsWith @x (const passed) (checkClosed vty)
   in TestCase .
      runTestIgnoreErrors
        checkClosedType
        (\(ty, _) -> checkTerm (eval [] ty) source)
        (assertBool "" False)
