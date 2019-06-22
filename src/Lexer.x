{

module Lexer(Lexer.lex, Token(..)) where

}

%wrapper "posn"

$digit = 0-9
$alpha = [a-z]

tokens :-
  $white+                               ;
  "//".*                                ;
  "algorithm"                           { tokenof TokenAlgorithm }
  "var"                                 { tokenof TokenVar }
  "int"                                 { tokenof TokenInt }
  "bool"                                { tokenof TokenBool }
  "string"                              { tokenof TokenString }
  "unit"                                { tokenof TokenUnit }
  "if"                                  { tokenof TokenIf }
  "else"                                { tokenof TokenElse }
  "while"                               { tokenof TokenWhile }
  "for"                                 { tokenof TokenFor }
  "return"                              { tokenof TokenReturn }
  "goto"                                { tokenof TokenGoto }
  "switch"                              { tokenof TokenSwitch }
  "case"                                { tokenof TokenCase }
  "default"                             { tokenof TokenDefault }
  "break"                               { tokenof TokenBreak }
  "continue"                            { tokenof TokenContinue }
  "ref"                                 { tokenof TokenRef }
  "effect"                              { tokenof TokenEffect }
  "function"                            { tokenof TokenFunction }
  "handler"                             { tokenof TokenHandler }
  "pure"                                { tokenof TokenPure }
  $alpha ("_"? ($alpha|$digit))*        { tokenof TokenIdentifier }
  $digit+                               { tokenof TokenNumberLiteral }
  [\"]([^\"\\]|[\\].)*[\"]              { tokenof TokenStringLiteral }
  "("                                   { tokenof TokenLeftParen }
  ")"                                   { tokenof TokenRightParen }
  "{"                                   { tokenof TokenLeftBrace }
  "}"                                   { tokenof TokenRightBrace }
  "="                                   { tokenof TokenAssign }
  ";"                                   { tokenof TokenSemicolon }
  ":"                                   { tokenof TokenColon }
  ","                                   { tokenof TokenComma }
  "+"                                   { tokenof TokenAdd }
  "-"                                   { tokenof TokenSub }
  "*"                                   { tokenof TokenMul }
  "/"                                   { tokenof TokenDiv }
  "%"                                   { tokenof TokenMod }
  "<"                                   { tokenof TokenLessThan }
  ">"                                   { tokenof TokenMoreThan }
  "=="                                  { tokenof TokenEquals }
  "!="                                  { tokenof TokenDiffs }
  "++"                                  { tokenof TokenIncr }
  "--"                                  { tokenof TokenDecr } 

{

data Token = TokenAlgorithm
           | TokenVar
           | TokenInt
           | TokenBool
           | TokenString
           | TokenScript
           | TokenUnit
           | TokenIf
           | TokenElse
           | TokenWhile
           | TokenFor
           | TokenReturn
           | TokenGoto
           | TokenSwitch
           | TokenCase
           | TokenDefault
           | TokenBreak
           | TokenContinue
           | TokenRef
           | TokenEffect
           | TokenFunction
           | TokenHandler
           | TokenPure
           | TokenIdentifier
           | TokenNumberLiteral
           | TokenStringLiteral
           | TokenLeftParen
           | TokenRightParen
           | TokenLeftBrace
           | TokenRightBrace
           | TokenAssign
           | TokenSemicolon
           | TokenColon
           | TokenComma
           | TokenAdd
           | TokenSub
           | TokenMul
           | TokenDiv
           | TokenMod
           | TokenLessThan
           | TokenMoreThan
           | TokenEquals
           | TokenDiffs
           | TokenIncr
           | TokenDecr
           deriving Show

lex = alexScanTokens

tokenof token (AlexPn _ line col) str = (line, col, str, token)

}
