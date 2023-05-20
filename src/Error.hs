module Error (
  TermString (..),
  Reportable (..),
  ParseError (..),
  ConversionError (..),
  ErrorDuringConversion (..),
  ErrorDuringUnification (..),
  InferenceError (..),
  CheckError (..),
)
where

import Error.Diagnose

import Parser.Lexer (Token)
import Syntax hiding (Type)

newtype TermString = TS {unTS :: String}

instance Show TermString where
  show = unTS

class Reportable e where
  report :: e -> Report String

createError :: String -> [(Position, Marker String)] -> Report String
createError msg ctx = Err Nothing msg [(pos, msg) | (pos, msg) <- ctx] []

data ParseError
  = UnexpectedEOF Position
  | UnexpectedToken Token Position
  | LexerError String

instance Reportable ParseError where
  report (UnexpectedEOF pos) =
    let msg = "Parse error."
        ctx = "Unexpected end of file."
     in createError msg [(pos, This ctx)]
  report (UnexpectedToken t pos) =
    let msg = "Parse error."
        ctx = "Unexpected token " ++ show t ++ "."
     in createError msg [(pos, This ctx)]
  report (LexerError msg) = createError msg []

data ConversionError
  = ErrorDuringConversion TermString TermString ErrorDuringConversion
  | ErrorDuringUnification TermString TermString ErrorDuringUnification

instance Reportable ConversionError where
  report (ErrorDuringConversion a b err) =
    let ctx = "While converting [" ++ unTS a ++ " ≡ " ++ unTS b ++ "]"
     in reportConvError ctx err
  report (ErrorDuringUnification a b err) =
    let ctx = "While converting [" ++ unTS a ++ " ≡ " ++ unTS b ++ "]"
     in reportUnifyError ctx err

data ErrorDuringConversion
  = ConversionBetweenUniverses Position
  | ConversionFailure TermString TermString Position
  | RigidSpineMismatch (Maybe TermString) (Maybe TermString) Position
  | MatchBranchMismatch Name Name Position
  | ConstructorMismatch Name Name Position

reportConvError :: String -> ErrorDuringConversion -> Report String
reportConvError while (ConversionBetweenUniverses pos) =
  let msg = "Type conversion failed."
      ctx = "Cannot convert between universes."
   in createError msg [(pos, This ctx), (pos, Where while)]
reportConvError while (ConversionFailure a b pos) =
  let msg = "Type conversion failed."
      ctx = "Failed to convert [" ++ unTS a ++ " ≡ " ++ unTS b ++ "]."
   in createError msg [(pos, This ctx), (pos, Where while)]
reportConvError while (RigidSpineMismatch a b pos) =
  let msg = "Rigid neutral spine mismatch."
      ctx =
        case (a, b) of
          (Nothing, Nothing) -> "BUG: IMPOSSIBLE!"
          (Just a, Nothing) -> "Spines must have equal length (found extra eliminator [" ++ unTS a ++ "])"
          (Nothing, Just b) -> "Spines must have equal length (found extra eliminator [" ++ unTS b ++ "])"
          (Just a, Just b) -> "Could not match different eliminators [" ++ unTS a ++ " ≡ " ++ unTS b ++ "]"
   in createError msg [(pos, This ctx), (pos, Where while)]
reportConvError while (MatchBranchMismatch cons cons' pos) =
  let msg = "Type conversion failed."
      ctx = "Match expressions must have equal constructor names; found [" ++ cons ++ " ≢ " ++ cons' ++ "]."
   in createError msg [(pos, This ctx), (pos, Where while)]
reportConvError while (ConstructorMismatch cons cons' pos) =
  let msg = "Type conversion failed."
      ctx = "Inductive types must have equal constructor names; found [" ++ cons ++ " ≢ " ++ cons' ++ "]."
   in createError msg [(pos, This ctx), (pos, Where while)]

data ErrorDuringUnification
  = NonLinearSpineDuplicate Name Position
  | NonLinearSpineNonVariable TermString Position
  | EscapingVariable Name Position
  | OccursCheck MetaVar Position
  | NElimInSpine MetaVar Position
  | JInSpine MetaVar Position
  | QElimInSpine MetaVar Position
  | MatchInSpine MetaVar Position

reportUnifyError :: String -> ErrorDuringUnification -> Report String
reportUnifyError while (NonLinearSpineDuplicate name pos) =
  let msg = "Failed to invert non-linear spine during pattern unification."
      ctx = "Duplicate variable '" ++ name ++ "' present in spine."
   in createError msg [(pos, This ctx), (pos, Where while)]
reportUnifyError while (NonLinearSpineNonVariable t pos) =
  let msg = "Failed to invert non-linear spine during pattern unification."
      ctx = "Non-variable term [" ++ unTS t ++ "] present in spine."
   in createError msg [(pos, This ctx), (pos, Where while)]
reportUnifyError while (EscapingVariable name pos) =
  let msg = "Failed to rename value with substitution map."
      ctx = "Variable '" ++ name ++ "' escapes the metavariable scope."
   in createError msg [(pos, This ctx), (pos, Where while)]
reportUnifyError while (OccursCheck (MetaVar v) pos) =
  let msg = "Occurs check failed."
      ctx = "Occurs check failed solving metavariable [?" ++ show v ++ "] (it appears in its own solution)."
   in createError msg [(pos, This ctx), (pos, Where while)]
reportUnifyError while (NElimInSpine (MetaVar v) pos) =
  let msg = "Unsolvable metavariable."
      ctx = "Cannot solve metavariable [?" ++ show v ++ "] as it is eliminated by a ℕ recursor."
   in createError msg [(pos, This ctx), (pos, Where while)]
reportUnifyError while (JInSpine (MetaVar v) pos) =
  let msg = "Unsolvable metavariable."
      ctx = "Cannot solve metavariable [?" ++ show v ++ "] as it is eliminated by J term."
   in createError msg [(pos, This ctx), (pos, Where while)]
reportUnifyError while (QElimInSpine (MetaVar v) pos) =
  let msg = "Unsolvable metavariable."
      ctx = "Cannot solve metavariable [?" ++ show v ++ "] as it is eliminated by quotient eliminator term."
   in createError msg [(pos, This ctx), (pos, Where while)]
reportUnifyError while (MatchInSpine (MetaVar v) pos) =
  let msg = "Unsolvable metavariable."
      ctx = "Cannot solve metavariable [?" ++ show v ++ "] as it is eliminated by match term."
   in createError msg [(pos, This ctx), (pos, Where while)]

data InferenceError
  = VariableOutOfScope Name Position
  | ApplicationHead TermString Position
  | FstProjectionHead TermString Position
  | SndProjectionHead TermString Position
  | ReflIrrelevant TermString Position
  | SymmetryIrrelevant TermString Position
  | TransitivityIrrelevant TermString Position
  | CongruenceDomainIrrelevant TermString Position
  | TranspIrrelevant TermString Position
  | CastBetweenUniverses Relevance Position Relevance Position
  | QuotientHead TermString Position
  | IdReflIrrelevant TermString Position
  | ConstructorNotInTypeMatch Name TermString Position
  | NonTotalMatch [Name] Position
  | FLiftNotInductiveType TermString Position
  | FmapNeedsFunctorInstance Position
  | MatchHead TermString Position
  | FixAnnotation TermString Position
  | FixViewWithNoFunctor Position
  | InductiveTypeFamily TermString Position
  | InductiveTypeConstructor Name Name Position
  | BoxElimHead TermString Position
  | InferenceFailure Position

instance Reportable InferenceError where
  report (VariableOutOfScope name pos) =
    let msg = "Variable not in scope."
        ctx = "Variable '" ++ name ++ "' is not defined."
     in createError msg [(pos, This ctx)]
  report (ApplicationHead t pos) =
    let msg = "Expected Π (Pi) type."
        ctx = "Expected Π type but found [" ++ unTS t ++ "]"
     in createError msg [(pos, This ctx)]
  report (FstProjectionHead t pos) =
    let msg = "Expected ∃ (Exists) or Σ (Sigma) type in first projection."
        ctx = "Expected ∃ or Σ type, but found ̈[" ++ unTS t ++ "]"
     in createError msg [(pos, This ctx)]
  report (SndProjectionHead t pos) =
    let msg = "Expected ∃ (Exists) or Σ (Sigma) type in second projection"
        ctx = "Expected ∃ or Σ type, but found ̈[" ++ unTS t ++ "]"
     in createError msg [(pos, This ctx)]
  report (ReflIrrelevant t pos) =
    let msg =
          "Reflexivity must only witness equalities of relevant types \
          \ (irrelevant types are trivially convertible)."
        ctx = "Term has type [" ++ unTS t ++ "] which is irrelevant."
     in createError msg [(pos, This ctx)]
  report (SymmetryIrrelevant t pos) =
    let msg =
          "Symmetry must only witness equalities of relevant types \
          \ (irrelevant types are trivially convertible)."
        ctx = "Term has type [" ++ unTS t ++ "] which is irrelevant."
     in createError msg [(pos, This ctx)]
  report (TransitivityIrrelevant t pos) =
    let msg =
          "Transitivity must only witness equalities of relevant types \
          \ (irrelevant types are trivially convertible)."
        ctx = "Term has type [" ++ unTS t ++ "] which is irrelevant."
     in createError msg [(pos, This ctx)]
  report (CongruenceDomainIrrelevant t pos) =
    let msg =
          "Congruence [ap] function domain must only witness equalities of \
          \ relevant types (irrelevant types are trivially convertible)."
        ctx = "Term has type [" ++ unTS t ++ "] which is irrelevant."
     in createError msg [(pos, This ctx)]
  report (TranspIrrelevant t pos) =
    let msg = "Can only transport along relevant types."
        ctx = "Term has type [" ++ unTS t ++ "] which is irrelevant."
     in createError msg [(pos, This ctx)]
  report (CastBetweenUniverses s pos s' pos') =
    let msg = "Cast types must live in the same universe."
        ctxA = "Type has sort [" ++ show s ++ "]."
        ctxB = "Type has sort [" ++ show s' ++ "]."
     in createError msg [(pos, This ctxA), (pos', This ctxB)]
  report (QuotientHead t pos) =
    let msg = "Expected Quotient (A/R) type in quotient eliminator."
        ctx = "Expected Quotient type, but found ̈[" ++ unTS t ++ "]."
     in createError msg [(pos, This ctx)]
  report (IdReflIrrelevant t pos) =
    let msg = "Can only form inductive equality type over relevant types."
        ctx = "Term has type [" ++ unTS t ++ "] which is irrelevant."
     in createError msg [(pos, This ctx)]
  report (ConstructorNotInTypeMatch c t pos) =
    let msg = "Constructor not in type found in match expression."
        ctx = "Matching on type [" ++ unTS t ++ "] which does not contain constructor [" ++ c ++ "]."
     in createError msg [(pos, This ctx)]
  report (NonTotalMatch missing pos) =
    let msg = "Match expression is not total."
        ctx = "Missing cases are " ++ show (map TS missing) ++ "."
     in createError msg [(pos, This ctx)]
  report (FLiftNotInductiveType t pos) =
    let msg = "Functor lift must be supplied with inductive type."
        ctx = "Expected inductive type, but found [" ++ unTS t ++ "]."
     in createError msg [(pos, This ctx)]
  report (FmapNeedsFunctorInstance pos) =
    let msg = "No functor instance found."
        ctx = "Inductive type needs functor instance to use [fmap]."
     in createError msg [(pos, This ctx)]
  report (MatchHead t pos) =
    let msg = "Expected inductive type (μF. t) in argument of match expression."
        ctx = "Expected inductive type, but found [" ++ unTS t ++ "]."
     in createError msg [(pos, This ctx)]
  report (FixAnnotation t pos) =
    let msg = "Fixed point must be annotated with inductive type."
        ctx = "Expected inductive type (μF. t) in fixed point annotation, but found [" ++ unTS t ++ "]."
     in createError msg [(pos, This ctx)]
  report (FixViewWithNoFunctor pos) =
    let msg = "Fixed point with view requires functor instance."
        ctx = "The provided inductive type has no functor instance."
     in createError msg [(pos, This ctx)]
  report (InductiveTypeFamily t pos) =
    let msg = "Inductive type must be a type family (A → U)."
        ctx = "Expected proof relevant indexed type family, but found [" ++ unTS t ++ "]."
     in createError msg [(pos, This ctx)]
  report (InductiveTypeConstructor f f' pos) =
    let msg = "Inductive type constructors must construct correct type."
        ctx = "Constructor in type [" ++ f ++ "] attempts to construct in [" ++ f' ++ "]."
     in createError msg [(pos, This ctx)]
  report (BoxElimHead t pos) =
    let msg = "Expected Box (▢A) type in quotient eliminator."
        ctx = "Expected Box type, but found ̈[" ++ unTS t ++ "]."
     in createError msg [(pos, This ctx)]
  report (InferenceFailure pos) =
    let msg = "Type inference failed (try adding a type annotation)."
        ctx = "Could not infer type for term."
     in createError msg [(pos, This ctx)]

data CheckError
  = CheckType TermString Position
  | CheckLambda TermString Position
  | CheckPropPair TermString Position
  | CheckPair TermString Position
  | CheckQuotientProj TermString Position
  | CheckIdPath TermString Position
  | ConstructorNotInTypeCons Name TermString Position
  | CheckCons TermString Name Position
  | ConstructorIndexSortUnknown Position
  | CheckIn TermString Position
  | CheckBoxProof TermString Position

instance Reportable CheckError where
  report (CheckType t pos) =
    let msg = "Expected type, but found term."
        ctx = "Term has type [" ++ unTS t ++ "]; expected a universe sort."
     in createError msg [(pos, This ctx)]
  report (CheckLambda t pos) =
    let msg = "λ-expression type checking failed."
        ctx = "Checking λ-expression against type [" ++ unTS t ++ "] failed (expected Π type)."
     in createError msg [(pos, This ctx)]
  report (CheckPropPair t pos) =
    let msg = "Propositional pair type checking failed."
        ctx = "Checking propositional pair against type [" ++ unTS t ++ "] failed (expected ∃ type)."
     in createError msg [(pos, This ctx)]
  report (CheckPair t pos) =
    let msg = "Pair type checking failed."
        ctx = "Checking pair against type [" ++ unTS t ++ "] failed (expected Σ type)."
     in createError msg [(pos, This ctx)]
  report (CheckQuotientProj t pos) =
    let msg = "Checking quotient projection against type [" ++ unTS t ++ "] failed (expected Quotient (A/R) type)."
        ctx = "Could not infer type for term."
     in createError msg [(pos, This ctx)]
  report (CheckIdPath t pos) =
    let msg = "Idpath type checking failed."
        ctx = "Checking Idpath argument against type [" ++ unTS t ++ "] failed (expected inductive identity type Id(A, t, u))."
     in createError msg [(pos, This ctx)]
  report (ConstructorNotInTypeCons c t pos) =
    let msg = "Constructor not in type."
        ctx =
          "Checking against inductive type ["
            ++ unTS t
            ++ "] which does not contain constructor ["
            ++ c
            ++ "]."
     in createError msg [(pos, This ctx)]
  report (CheckCons t c pos) =
    let msg = "Constructor type checking failed."
        ctx =
          "Checking constructor ["
            ++ c
            ++ "] against type ["
            ++ unTS t
            ++ "] failed (expected inductive type containing constructor)."
     in createError msg [(pos, This ctx)]
  report (ConstructorIndexSortUnknown pos) =
    let msg = "Checking constructor failed."
        ctx = "Index type of inductive type is unknown, but necessary to check the equality proof term in the constructor."
     in createError msg [(pos, This ctx)]
  report (CheckIn t pos) =
    let msg = "Checking inductive injection failed."
        ctx = "Checking [in] against type [" ++ unTS t ++ "] failed (expected an applied inductive type (μF p))"
     in createError msg [(pos, This ctx)]
  report (CheckBoxProof t pos) =
    let msg = "Box proof type checking failed."
        ctx = "Checking Box proof argument against type [" ++ unTS t ++ "] failed (expected Box (▢A) type)."
     in createError msg [(pos, This ctx)]
