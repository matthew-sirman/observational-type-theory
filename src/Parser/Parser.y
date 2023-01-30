{
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Parser.Parser where

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
  transp                { L _ KWTransp }
  cast                  { L _ KWCast }
  castrefl              { L _ KWCastRefl }
  let                   { L _ KWLet }
  '='                   { L _ TokEquals }
  in                    { L _ KWIn }
  var                   { L _ (TokName _) }

%right in
%right '->'
%right '.'

%%

rel :: { Loc Relevance }
  : U                                                               { loc Relevant $1 $> }
  | O                                                               { loc Irrelevant $1 $> }

exp :: { Raw }
  : '\\' var '.' exp                                                { rloc (LambdaF (projName $2) $4) $1 $> }
  | let var ':' exp '=' exp in exp                                  { rloc (LetF (projName $2) $4 $6 $8) $1 $> }
  | term                                                            { $1 }

term :: { Raw }
  : '(' var ':' rel exp ')' '->' term                               { rloc (PiF (syntax $4) (projName $2) $5 $8) $1 $> }
  | Exists '(' var ':' exp ')' '.' term                             { rloc (ExistsF (projName $3) $5 $8) $1 $> }
  | apps '/\\' apps                                                 { rloc (ExistsF "_" $1 $3) $1 $> }
  | term '~' '[' exp ']' term                                       { rloc (EqF $1 $4 $6) $1 $> }
  | apps                                                            { $1 }

apps :: { Raw }
  : apps atom                                                       { rloc (AppF $1 $2) $1 $> }
  | S atom                                                          { rloc (SuccF $2) $1 $> }
  | rec '(' var '.' exp ',' exp ',' var var '.' exp ',' exp ')'     { rloc (NElimF (projName $3) $5 $7 (projName $9) (projName $10) $12 $14) $1 $> }
  | fst atom                                                        { rloc (FstF $2) $1 $> }
  | snd atom                                                        { rloc (SndF $2) $1 $> }
  | abort '(' exp ',' exp ')'                                       { rloc (AbortF $3 $5) $1 $> }
  | refl atom                                                       { rloc (ReflF $2) $1 $> }
  | transp '(' exp ',' var var '.' exp ',' exp ',' exp ',' exp ')'  { rloc (TranspF $3 (projName $5) (projName $6) $8 $10 $12 $14) $1 $> }
  | cast '(' exp ',' exp ',' exp ',' exp ')'                        { rloc (CastF $3 $5 $7 $9) $1 $> }
  | castrefl '(' exp ',' exp ')'                                    { rloc (CastReflF $3 $5) $1 $> }
  | atom                                                            { $1 }

atom :: { Raw }
  : var                                                             { rloc (VarF (projName $1)) $1 $> }
  | rel                                                             { Fix (RawF (fmap UF $1)) }
  | '0'                                                             { rloc ZeroF $1 $> }
  | Nat                                                             { rloc NatF $1 $> }
  | '<' exp ',' exp '>'                                             { rloc (PairF $2 $4) $1 $> }
  | Empty                                                           { rloc EmptyF $1 $> }
  | '*'                                                             { rloc OneF $1 $> }
  | Unit                                                            { rloc UnitF $1 $> }
  | '(' exp ':' exp ')'                                             { rloc (AnnotationF $2 $4) $1 $>}
  | '(' exp ')'                                                     { $2 }

{

type Parser a = StateT AlexState (Except (Err.Report String)) a

liftAlex :: forall a. Alex a -> Parser a
liftAlex alex =
  StateT (boxError . unAlex alex)
  where
    boxError :: Either String (AlexState, a) -> Except (Err.Report String) (a, AlexState)
    boxError (Left msg) = throwError (Err.Err Nothing msg [] [])
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

rloc :: (Located start, Located end) => TermF Name Raw -> start -> end -> Raw
rloc e start end = Fix (RawF (loc e start end))

parseError :: Loc Token -> Parser a
parseError (L _ TokEOF) = do
  ((AlexPn _ line col), _, _, input) <- liftAlex alexGetInput
  let msg = "Unexpected end of file."
      pos = Err.Position (line, col) (line, col) "<test-file>"
  throwError (Err.Err Nothing "Parse error." [(pos, Err.This msg)] [])
parseError (L pos t) = do
  let msg = "Unexpected token " ++ show t ++ "."
  throwError (Err.Err Nothing "Parse error." [(pos, Err.This msg)] [])

lexer :: (Loc Token -> Parser a) -> Parser a
lexer continuation = do
  nextToken <- liftAlex alexMonadScan
  continuation nextToken

parse :: String -> Either (Err.Report String) Raw
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
