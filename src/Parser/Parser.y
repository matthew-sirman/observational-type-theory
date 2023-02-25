{
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Parser.Parser where

import Error
import Parser.Lexer
import Syntax

import Control.Monad.State
import Control.Monad.Except
import Data.Fix (Fix (..))
import qualified Error.Diagnose as Err

}

%name parser exp

%tokentype { Loc Token }
%error { parseError }
%monad { Parser }
%lexer { lexer } { L _ TokEOF }

%token
  U                     { L _ SymUnivRelevant }
  O                     { L _ SymUnivIrrelevant }
  '\\'                  { L _ SymLambda }
  '('                   { L _ TokOpenParenthesis }
  ')'                   { L _ TokCloseParenthesis }
  ':'                   { L _ TokColon }
  '->'                  { L _ SymArrow }
  '0'                   { L _ SymZero }
  S                     { L _ SymSucc }
  rec                   { L _ KWNElim }
  Nat                   { L _ SymNat }
  '<'                   { L _ TokOpenAngle }
  '>'                   { L _ TokCloseAngle }
  fst                   { L _ KWFst }
  snd                   { L _ KWSnd }
  Exists                { L _ SymExists }
  '.'                   { L _ TokDot }
  ','                   { L _ TokComma }
  '/\\'                 { L _ SymAnd }
  abort                 { L _ KWAbort }
  Empty                 { L _ SymEmpty }
  '*'                   { L _ SymOne }
  Unit                  { L _ SymUnit }
  '~'                   { L _ SymEq }
  '['                   { L _ TokOpenBracket }
  ']'                   { L _ TokCloseBracket }
  refl                  { L _ KWRefl }
  sym                   { L _ KWSym }
  trans                 { L _ KWTrans }
  ap                    { L _ KWAp }
  transp                { L _ KWTransp }
  cast                  { L _ KWCast }
  castrefl              { L _ KWCastRefl }
  Sigma                 { L _ SymSigma }
  times                 { L _ SymTimes }
  ';'                   { L _ SymSemiColon }
  '/'                   { L _ SymForwardSlash }
  proj                  { L _ SymQProj }
  Qelim                 { L _ KWQElim }
  Idrefl                { L _ KWIdRefl }
  Idpath                { L _ KWIdPath }
  J                     { L _ KWJ }
  Id                    { L _ KWId }
  match                 { L _ KWMatch }
  as                    { L _ KWAs }
  return                { L _ KWReturn }
  with                  { L _ KWWith }
  '|'                   { L _ TokPipe }
  let                   { L _ KWLet }
  '='                   { L _ TokEquals }
  in                    { L _ KWIn }
  '_'                   { L _ TokHole }
  var                   { L _ (TokName _) }

%right in
%right '->'
%right '.'

%%

rel :: { Loc (RelevanceF ()) }
  : U                                                               { loc Relevant $1 $> }
  | O                                                               { loc Irrelevant $1 $> }
  | '_'                                                             { loc SortHole $1 $> }

exp :: { Raw }
  : '\\' binder '.' exp                                             { rloc (LambdaF $2 $4) $1 $> }
  | let binder ':' exp '=' exp in exp                               { rloc (LetF $2 $4 $6 $8) $1 $> }
  | match exp as binder return exp with branches                    { rloc (MatchF $2 $4 $6 $8) $1 $7 }
  | term                                                            { $1 }

term :: { Raw }
  : '(' binder ':' rel exp ')' '->' term                            { rloc (PiF (syntax $4) $2 $5 $8) $1 $> }
  | apps '->' term                                                  { rloc (PiF SortHole Hole $1 $3) $1 $> }
  | Exists '(' binder ':' exp ')' '.' term                          { rloc (ExistsF $3 $5 $8) $1 $> }
  | apps '/\\' apps                                                 { rloc (ExistsF Hole $1 $3) $1 $> }
  | apps '~' '[' exp ']' apps                                       { rloc (EqF $1 $4 $6) $1 $> }
  | apps '~' apps                                                   { rloc (EqF $1 (rloc HoleF $2 $2) $3) $1 $> }
  | Sigma '(' binder ':' exp ')' '.' term                           { rloc (SigmaF $3 $5 $8) $1 $> }
  | apps times apps                                                 { rloc (SigmaF Hole $1 $3) $1 $> }
  | atom '/' '(' binder binder '.' exp ','
                 binder '.' exp ','
                 binder binder binder '.' exp ','
                 binder binder binder binder binder '.' exp
             ')'                                                    { rloc (QuotientF $1 $4 $5 $7
                                                                                         $9 $11
                                                                                         $13 $14 $15 $17
                                                                                         $19 $20 $21 $22 $23 $25) $1 $> }
  | apps                                                            { $1 }

apps :: { Raw }
  : apps atom                                                       { rloc (AppF $1 $2) $1 $> }
  | S atom                                                          { rloc (SuccF $2) $1 $> }
  | rec '(' binder '.' exp ',' exp ','
            binder binder '.' exp ',' exp ')'                       { rloc (NElimF $3 $5 $7 $9 $10 $12 $14) $1 $> }
  | fst atom                                                        { rloc (FstF () $2) $1 $> }
  | snd atom                                                        { rloc (SndF () $2) $1 $> }
  | abort '(' exp ',' exp ')'                                       { rloc (AbortF $3 $5) $1 $> }
  | refl atom                                                       { rloc (ReflF $2) $1 $> }
  | sym '(' exp ',' exp ',' exp ')'                                 { rloc (SymF $3 $5 $7) $1 $> }
  | sym atom                                                        { rloc (SymF (rloc HoleF $1 $1) (rloc HoleF $1 $1) $2) $1 $> }
  | trans '(' exp ',' exp ',' exp ',' exp ',' exp ')'               { rloc (TransF $3 $5 $7 $9 $11) $1 $> }
  | ap '(' exp ',' binder '.' exp ',' exp ',' exp ',' exp ')'       { rloc (ApF $3 $5 $7 $9 $11 $13) $1 $> }
  | transp '(' exp ',' binder binder '.' exp ','
               exp ',' exp ',' exp ')'                              { rloc (TranspF $3 $5 $6 $8 $10 $12 $14) $1 $> }
  | cast '(' exp ',' exp ',' exp ',' exp ')'                        { rloc (CastF $3 $5 $7 $9) $1 $> }
  | castrefl '(' exp ',' exp ')'                                    { rloc (CastReflF $3 $5) $1 $> }
  | proj atom                                                       { rloc (QProjF $2) $1 $> }
  | Qelim '(' binder '.' exp ','
              binder '.' exp ','
              binder binder binder '.' exp ','
              exp
          ')'                                                       { rloc (QElimF $3 $5
                                                                                   $7 $9
                                                                                   $11 $12 $13 $15
                                                                                   $17) $1 $> }
  | Idrefl atom                                                     { rloc (IdReflF $2) $1 $> }
  | Idpath atom                                                     { rloc (IdPathF $2) $1 $> }
  | J '(' exp',' exp',' binder binder '.' exp','
          exp',' exp',' exp ')'                                     { rloc (JF $3 $5 $7 $8 $10 $12 $14 $16) $1 $> }
  | Id '(' exp ',' exp ',' exp ')'                                  { rloc (IdF $3 $5 $7) $1 $> }
  | atom                                                            { $1 }

atom :: { Raw }
  : var                                                             { rloc (VarF (projName $1)) $1 $> }
  | '_'                                                             { rloc HoleF $1 $> }
  | rel                                                             { Fix (RawF (fmap UF $1)) }
  | '0'                                                             { rloc ZeroF $1 $> }
  | Nat                                                             { rloc NatF $1 $> }
  | '<' exp ',' exp '>'                                             { rloc (PropPairF $2 $4) $1 $> }
  | Empty                                                           { rloc EmptyF $1 $> }
  | '*'                                                             { rloc OneF $1 $> }
  | Unit                                                            { rloc UnitF $1 $> }
  | '(' exp ';' exp ')'                                             { rloc (PairF $2 $4) $1 $> }
  | '(' exp ':' exp ')'                                             { rloc (AnnotationF $2 $4) $1 $>}
  | '(' exp ')'                                                     { $2 }

branches :: { [RawBranch] }
  : {-# empty #-}                                                   { [] }
  | '|' pattern '->' exp branches                                   { BranchF $2 $4 : $5 }

pattern :: { Pattern }
  : '0'                                                             { ZeroP }
  | S binder                                                        { SuccP $2 }

binder :: { Binder }
  : var                                                             { Name (projName $1) }
  | '_'                                                             { Hole }

{

type Parser a = StateT AlexState (Except ParseError) a

liftAlex :: forall a. Alex a -> Parser  a
liftAlex alex =
  StateT (boxError . unAlex alex)
  where
    boxError :: Either String (AlexState, a) -> Except ParseError (a, AlexState)
    boxError (Left msg) = throwError (LexerError msg)
    boxError (Right (s, a)) = pure (a, s)

class Located a where
  projectLoc :: a -> Err.Position

instance Located (Loc a) where
  projectLoc = location

instance Located (RawF a) where
  projectLoc (RawF l) = projectLoc l

instance Located (Fix RawF) where
  projectLoc (Fix r) = projectLoc r

projName :: Loc Token -> Name
projName (L _ (TokName n)) = n
projName (L _ t) = error ("BUG: Tried to project the name of token " ++ show t)

loc :: (Located start, Located end) => a -> start -> end -> Loc a
loc element start end =
  let s = projectLoc start
      e = projectLoc end
  in L
       { syntax = element,
         location = Err.Position (Err.begin s) (Err.end e) (Err.file s)
       }

rloc :: (Located start, Located end) => TermF () () Name Raw -> start -> end -> Raw
rloc e start end = Fix (RawF (loc e start end))

parseError :: Loc Token -> Parser a
parseError (L _ TokEOF) = do
  ((AlexPn _ line col), _, _, input) <- liftAlex alexGetInput
  let pos = Err.Position (line, col) (line, col) "<test-file>"
  throwError (UnexpectedEOF pos)
parseError (L pos t) = do
  throwError (UnexpectedToken t pos)

lexer :: (Loc Token -> Parser a) -> Parser a
lexer continuation = do
  nextToken <- liftAlex alexMonadScan
  continuation nextToken

parse :: String -> Either ParseError Raw
parse input = runExcept (evalStateT parser initState)
  where
    initState :: AlexState
    initState =
      AlexState
        { alex_pos = alexStartPos
        , alex_inp = input
        , alex_chr = '\n'
        , alex_scd = 0
        , alex_bytes = []
        }

}
