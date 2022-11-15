module Parser where

import Parser.Lexer
import Parser.Parser
import Syntax

testParse :: String -> IO ()
testParse input =
  case runAlex input parser of
    Left e -> putStrLn e
    Right raw -> putStrLn (prettyPrintTermDebug False [] (eraseSourceLocations raw))
