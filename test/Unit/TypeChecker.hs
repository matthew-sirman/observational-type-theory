{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}

module Unit.TypeChecker where

import Test.HUnit
import Text.RawString.QQ

import Error

import Unit.TestEnvironment

typeUniverse :: Test
typeUniverse =
  TestLabel "Universe type checking" $
  TestList
    [ "Relevant universe has type [U]" ~: programTypeChecks [r|U|] [r|U|]
    , "Irrelevant universe has type [U]" ~: programTypeChecks [r|Ω|] [r|U|]
    ]

typeLambda :: Test
typeLambda =
  TestLabel "Lambda term type checking" $
  TestList
    [ "Relevant lambda has [Π] type" ~:
      programTypeChecks [r|λx. 0|] [r|(x :U ℕ) -> ℕ|]
    , "Irrelevant lambda has [Π] type" ~:
      programTypeChecks [r|λx. *|] [r|(x :Ω ⊤) -> ⊤|]
    , "Unused domain type unrestricted" ~:
      programTypeChecks [r|λx. *|] [r|(x :Ω ⊥) -> ⊤|]
    , "Cross-universe (Prop -> Type)" ~:
      programTypeChecks [r|λx. 0|] [r|(x :Ω ⊤) -> ℕ|]
    , "Cross-domains (Type -> Prop)" ~:
      programTypeChecks [r|λx. *|] [r|(x :U ℕ) -> ⊤|]
    , "Non-[Π] type" ~: programFailsWith @CheckError [r|λx. x|] [r|⊤|]
    ]

typeApp :: Test
typeApp =
  TestLabel "Application term type checking" $
  TestList
    [ "Natural number identity application" ~:
      programTypeChecks [r|(λx. x : (x :U ℕ) -> ℕ) 0|] [r|ℕ|]
    , "Unannotated non-normal form application fails" ~:
      programFailsWith @InferenceError [r|(λx. x) 0|] [r|ℕ|]
    , "Irrelevant application" ~:
      programTypeChecks [r|(λx. x : (x :Ω ⊤) -> ⊤) *|] [r|⊤|]
    , "Cross-universe (Prop -> Type)" ~:
      programTypeChecks [r|(λx. 0 : (x :Ω ⊤) -> ℕ) *|] [r|ℕ|]
    , "Cross-universe (Type -> Prop)" ~:
      programTypeChecks [r|(λx. * : (x :U ℕ) -> ⊤) 0|] [r|⊤|]
    , "Type enforced even on unused argument" ~:
      programFailsWith @ConversionError [r|(λx. * : (x :U ℕ) -> ⊤) *|] [r|⊤|]
    , "Application head non-function type" ~:
      programFailsWith @InferenceError [r|0 0|] [r|ℕ|]
    ]

typePi :: Test
typePi =
  TestLabel "Pi term type checking" $
  TestList
    [ "Type -> Type" ~: programTypeChecks [r|(x :U U) -> U|] [r|U|]
    , "Prop -> Prop" ~: programTypeChecks [r|(x :U Ω) -> Ω|] [r|U|]
    , "Type -> Prop" ~: programTypeChecks [r|(x :U U) -> Ω|] [r|U|]
    , "Prop -> Type" ~: programTypeChecks [r|(x :U Ω) -> U|] [r|U|]
    , "Domain must be type" ~:
      programFailsWith @ConversionError [r|(x :U 0) -> U|] [r|U|]
    , "Codomain must be type" ~:
      programFailsWith @CheckError [r|(x :U U) -> 0|] [r|U|]
    , "Domain sort must match" ~:
      programFailsWith @ConversionError [r|(x :Ω ℕ) -> ℕ|] [r|U|]
    , "Codomain sort must match" ~:
      programFailsWith @ConversionError [r|(x :U ℕ) -> ℕ|] [r|Ω|]
    ]

typeZero :: Test
typeZero =
  TestLabel "Zero term type checking" $
  TestList
    [ "Checks as Nat" ~: programTypeChecks [r|0|] [r|ℕ|]
    , "Fails as universe" ~: programFailsWith @ConversionError [r|0|] [r|U|]
    ]

typeSucc :: Test
typeSucc =
  TestLabel "Succ term type checking" $
  TestList
    [ "[S 0] checks as Nat" ~: programTypeChecks [r|S 0|] [r|ℕ|]
    , "x:ℕ ⊢ [S x] : ℕ" ~: programTypeChecks [r|λx. S x|] [r|(x :U ℕ) → ℕ|]
    , "Fails on non-Nat subterm" ~:
      programFailsWith @ConversionError [r|S U|] [r|ℕ|]
    , "Fails as universe" ~: programFailsWith @ConversionError [r|S 0|] [r|U|]
    ]

typeNatElim :: Test
typeNatElim =
  TestLabel "Nat Elim Type Checking" $
  TestList
    [ "Identity eliminator" ~:
      programTypeChecks [r|λn. rec(z. ℕ, 0, _ k. S k, n)|] [r|(x :U ℕ) -> ℕ|]
    , "Argument must be natural" ~:
      programFailsWith
        @ConversionError
        [r|λn. rec(z. ℕ, 0, _ k. S k, n)|]
        [r|(x :U U) -> U|]
    , "Can eliminate into universe" ~:
      programTypeChecks [r|rec(z. Ω, ⊤, _ _. ⊥, 0)|] [r|Ω|]
    , "Branches must be consistent" ~:
      programFailsWith @ConversionError [r|rec(z. Ω, ⊤, _ _. *, 0)|] [r|Ω|]
    ]

allTests :: Test
allTests =
  TestList
    [typeUniverse, typeLambda, typeApp, typePi, typeZero, typeSucc, typeNatElim]
