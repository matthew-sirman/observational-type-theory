{
module Parser.Lexer where

import Syntax

}

%wrapper "monad"

$alpha = [a-zA-Z]

tokens :-
       $white+                  ;
       "--".*                   ;
       "U"                      { symbol SymUnivRelevant }
       "Ω"                      { symbol SymUnivIrrelevant }
       "O"                      { symbol SymUnivIrrelevant }
       "λ"                      { symbol SymLambda }
       "\\"                     { symbol SymLambda }
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
       "fst"                    { keyword KWFst }
       "snd"                    { keyword KWSnd }
       "∃"                      { symbol SymExists }
       "."                      { symbol TokDot }
       "∧"                      { symbol SymAnd }
       "/\\"                    { symbol SymAnd }
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

       [$alpha $digit \_ \']*   { identifier TokName }
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
  | KWFst
  | KWSnd
  | SymExists
  | TokDot
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
  deriving (Show)

keyword, symbol :: Token -> AlexInput -> Int -> Alex (Loc Token)
keyword t ((AlexPn start line _), _, _, _) len = pure (L (SLoc start (start + len) line) t)
symbol = keyword

identifier :: (Identifier -> Token) -> AlexInput -> Int -> Alex (Loc Token)
identifier t ((AlexPn start line _), _, _, input) len =
  pure (L (SLoc start (start + len) line) (t (take len input)))

}
