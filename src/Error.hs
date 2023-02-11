module Error where

import Error.Diagnose

import Parser.Lexer (Token)
import Syntax hiding (Type)

newtype TermString = TS {unTS :: String}

class Reportable e where
  report :: e -> Report String

createError :: String -> [(Position, String)] -> Report String
createError msg ctx = Err Nothing msg [(pos, This msg) | (pos, msg) <- ctx] []

data ParseError
  = UnexpectedEOF Position
  | UnexpectedToken Token Position
  | LexerError String

instance Reportable ParseError where
  report (UnexpectedEOF pos) =
    let msg = "Parse error."
        ctx = "Unexpected end of file."
     in createError msg [(pos, ctx)]
  report (UnexpectedToken t pos) =
    let msg = "Parse error."
        ctx = "Unexpected token " ++ show t ++ "."
     in createError msg [(pos, ctx)]
  report (LexerError msg) = createError msg []

data ConversionError
  = ConversionBetweenUniverses Position
  | ConversionFailure TermString TermString Position
  | RigidSpineMismatch (Maybe TermString) (Maybe TermString) Position

instance Reportable ConversionError where
  report (ConversionBetweenUniverses pos) =
    let msg = "Type conversion failed."
        ctx = "Cannot convert between universes."
     in createError msg [(pos, ctx)]
  report (ConversionFailure a b pos) =
    let msg = "Type conversion failed."
        ctx = "Failed to convert [" ++ unTS a ++ " ≡ " ++ unTS b ++ "]."
     in createError msg [(pos, ctx)]
  report (RigidSpineMismatch a b pos) =
    let msg = "Rigid neutral spine mismatch."
        ctx =
          case (a, b) of
            (Nothing, Nothing) -> "BUG: IMPOSSIBLE!"
            (Just a, Nothing) -> "Spines must have equal length (found extra eliminator [" ++ unTS a ++ "])"
            (Nothing, Just b) -> "Spines must have equal length (found extra eliminator [" ++ unTS b ++ "])"
            (Just a, Just b) -> "Could not match different eliminators [" ++ unTS a ++ " ≡ " ++ unTS b ++ "]"
     in createError msg [(pos, ctx)]

data InferenceError
  = VariableOutOfScope Name Position
  | ApplicationHead TermString Position
  | FstProjectionHead TermString Position
  | SndProjectionHead TermString Position
  | ReflIrrelevant TermString Position
  | TranspIrrelevant TermString Position
  | CastBetweenUniverses Relevance Position Relevance Position
  | QuotientHead TermString Position
  | IdReflIrrelevant TermString Position
  | InferenceFailure Position

instance Reportable InferenceError where
  report (VariableOutOfScope name pos) =
    let msg = "Variable not in scope."
        ctx = "Variable '" ++ name ++ "' is not defined."
     in createError msg [(pos, ctx)]
  report (ApplicationHead t pos) =
    let msg = "Expected Π (Pi) type."
        ctx = "Expected Π type but found [" ++ unTS t ++ "]"
     in createError msg [(pos, ctx)]
  report (FstProjectionHead t pos) =
    let msg = "Expected ∃ (Exists) or Σ (Sigma) type in first projection."
        ctx = "Expected ∃ or Σ type, but found ̈[" ++ unTS t ++ "]"
     in createError msg [(pos, ctx)]
  report (SndProjectionHead t pos) =
    let msg = "Expected ∃ (Exists) or Σ (Sigma) type in second projection"
        ctx = "Expected ∃ or Σ type, but found ̈[" ++ unTS t ++ "]"
     in createError msg [(pos, ctx)]
  report (ReflIrrelevant t pos) =
    let msg =
          "Refl must only witness equalities of relevant types \
          \ (irrelevant types are trivially convertible)."
        ctx = "Term has type [" ++ unTS t ++ "] which is irrelevant."
     in createError msg [(pos, ctx)]
  report (TranspIrrelevant t pos) =
    let msg = "Can only transport along relevant types."
        ctx = "Term has type [" ++ unTS t ++ "] which is irrelevant."
     in createError msg [(pos, ctx)]
  report (CastBetweenUniverses s pos s' pos') =
    let msg = "Cast types must live in the same universe."
        ctxA = "Type has sort [" ++ show s ++ "]."
        ctxB = "Type has sort [" ++ show s' ++ "]."
     in createError msg [(pos, ctxA), (pos', ctxB)]
  report (QuotientHead t pos) =
    let msg = "Expected Quotient (A/R) type in quotient eliminator."
        ctx = "Expected Quotient type, but found ̈[" ++ unTS t ++ "]."
     in createError msg [(pos, ctx)]
  report (IdReflIrrelevant t pos) =
    let msg = "Can only form inductive equality type over relevant types."
        ctx = "Term has type [" ++ unTS t ++ "] which is irrelevant."
     in createError msg [(pos, ctx)]
  report (InferenceFailure pos) =
    let msg = "Type inference failed (try adding a type annotation)."
        ctx = "Could not infer type for term."
     in createError msg [(pos, ctx)]

data CheckError
  = CheckType TermString Position
  | CheckLambda TermString Position
  | CheckPropPair TermString Position
  | CheckPair TermString Position
  | CheckQuotientProj TermString Position
  | CheckIdPath TermString Position

instance Reportable CheckError where
  report (CheckType t pos) =
    let msg = "Expected type, but found term."
        ctx = "Term has type [" ++ unTS t ++ "]; expected a universe sort."
     in createError msg [(pos, ctx)]
  report (CheckLambda t pos) =
    let msg = "λ-expression type checking failed."
        ctx = "Checking λ-expression against type [" ++ unTS t ++ "] failed (expected Π type)."
     in createError msg [(pos, ctx)]
  report (CheckPropPair t pos) =
    let msg = "Propositional pair type checking failed."
        ctx = "Checking propositional pair against type [" ++ unTS t ++ "] failed (expected ∃ type)."
     in createError msg [(pos, ctx)]
  report (CheckPair t pos) =
    let msg = "Pair type checking failed."
        ctx = "Checking pair against type [" ++ unTS t ++ "] failed (expected Σ type)."
     in createError msg [(pos, ctx)]
  report (CheckQuotientProj t pos) =
    let msg = "Checking quotient projection against type [" ++ unTS t ++ "] failed (expected Quotient (A/R) type)."
        ctx = "Could not infer type for term."
     in createError msg [(pos, ctx)]
  report (CheckIdPath t pos) =
    let msg = "Idpath type checking failed."
        ctx = "Checking Idpath argument against type [" ++ unTS t ++ "] failed (expected inductive identity type Id(A, t, u))."
     in createError msg [(pos, ctx)]
