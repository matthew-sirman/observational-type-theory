{
module Parser.Lexer where

import Syntax
import Error.Diagnose.Position(Position(..))

}

%wrapper "monad"

tokens :-
       $white+                  ;
       "--".*                   ;
       "U"                      { symbol SymUnivRelevant }
       "Ω"                      { symbol SymUnivIrrelevant }
       "O"                      { symbol SymUnivIrrelevant }
       "λ"                      { symbol SymLambda }
       "\"                      { symbol SymLambda }
       "("                      { symbol TokOpenParenthesis }
       ")"                      { symbol TokCloseParenthesis }
       ":"                      { symbol TokColon }
       "→"                      { symbol SymArrow }
       "->"                     { symbol SymArrow }
       "0"                      { symbol SymZero }
       "S"                      { symbol SymSucc}
       "ℕ-elim"                 { symbol KWNElim }
       "rec"                    { symbol KWNElim }
       "ℕ"                      { symbol SymNat }
       "Nat"                    { symbol SymNat }
       "⟨"                      { symbol TokOpenAngle }
       "<"                      { symbol TokOpenAngle }
       ">"                      { symbol TokCloseAngle }
       "⟩"                      { symbol TokCloseAngle }
       "fst"                    { keyword KWFst }
       "snd"                    { keyword KWSnd }
       "∃"                      { symbol SymExists }
       "."                      { symbol TokDot }
       ","                      { symbol TokComma }
       "∧"                      { symbol SymAnd }
       "/\"                     { symbol SymAnd }
       "⊥-elim"                 { keyword KWAbort }
       "abort"                  { keyword KWAbort }
       "⊥"                      { symbol SymEmpty }
       "Void"                   { symbol SymEmpty }
       "*"                      { symbol SymOne }
       "⊤"                      { symbol SymUnit }
       "Unit"                   { symbol SymUnit }
       "~"                      { symbol SymEq }
       "["                      { symbol TokOpenBracket }
       "]"                      { symbol TokCloseBracket }
       "refl"                   { keyword KWRefl }
       "transp"                 { keyword KWTransp }
       "cast"                   { keyword KWCast }
       "castrefl"               { keyword KWCastRefl }
       "let"                    { keyword KWLet }
       "="                      { symbol TokEquals }
       "in"                     { keyword KWIn}

       [a-z A-Z 0-9 \_ \']+   { identifier TokName }
{

data Token
  = SymUnivRelevant
  | SymUnivIrrelevant
  | SymLambda
  | TokOpenParenthesis
  | TokCloseParenthesis
  | TokColon
  | SymArrow
  | SymZero
  | SymSucc
  | KWNElim
  | SymNat
  | TokOpenAngle
  | TokCloseAngle
  | KWFst
  | KWSnd
  | SymExists
  | TokDot
  | TokComma
  | SymAnd
  | KWAbort
  | SymEmpty
  | SymOne
  | SymUnit
  | SymEq
  | TokOpenBracket
  | TokCloseBracket
  | KWRefl
  | KWTransp
  | KWCast
  | KWCastRefl
  | KWLet
  | TokEquals
  | KWIn
  | TokName Name
  | TokEOF
  deriving (Show)

keyword, symbol :: Token -> AlexInput -> Int -> Alex (Loc Token)
keyword t ((AlexPn _ line col), _, _, _) len = pure (L (Position (line, col) (line, col + len) "<test-file>") t)
symbol = keyword

identifier :: (Name -> Token) -> AlexInput -> Int -> Alex (Loc Token)
identifier t ((AlexPn _ line col), _, _, input) len =
  pure (L (Position (line, col) (line, col + len) "<test-file>") (t (take len input)))

alexEOF :: Alex (Loc Token)
alexEOF = pure (L (Position (0, 0) (0, 0) "<test-file>") TokEOF)

}
