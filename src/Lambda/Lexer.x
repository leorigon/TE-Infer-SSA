{
module Lambda.Lexer(Lambda.Lexer.lex, Token(..)) where
}

%wrapper "posn"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-

  $white+                               ;
  "--".*                                ;
  "let"                                 { tokenof TokenLet }
  "in"                                  { tokenof TokenIn }
  "true"                                { tokenof TokenTrue }
  "false"                               { tokenof TokenFalse }
  "if"                                  { tokenof TokenIf }
  "then"                                { tokenof TokenThen }
  "else"                                { tokenof TokenElse }
  "\"|"λ"                               { tokenof TokenLambda }
  "("                                   { tokenof TokenLParen }
  ")"                                   { tokenof TokenRParen }
  ","                                   { tokenof TokenComma }
  "="                                   { tokenof TokenEquals }
  "."                                   { tokenof TokenDot }
  "+"                                   { tokenof TokenPlus }
  "-"                                   { tokenof TokenMinus }
  "*"                                   { tokenof TokenTimes }
  "/"                                   { tokenof TokenDiv }
  "<"                                   { tokenof TokenLess }
  ">"                                   { tokenof TokenMore }
  $alpha ($alpha|$digit)*               { tokenof TokenIdentifier }
  $digit+                               { tokenof TokenNumber }
{
data Token = TokenLet
           | TokenIn
           | TokenTrue
           | TokenFalse
           | TokenIf
           | TokenThen
           | TokenElse
           | TokenLambda
           | TokenLParen
           | TokenRParen
           | TokenComma
           | TokenEquals
           | TokenDot
           | TokenPlus
           | TokenMinus
           | TokenTimes
           | TokenDiv
           | TokenLess
           | TokenMore
           | TokenIdentifier
           | TokenNumber
           deriving Show
lex = alexScanTokens
tokenof token (AlexPn _ line col) str =
  (line, col, str, token)
}
