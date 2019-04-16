{
module Lambda.Parser(parse) where

import qualified Lambda.Lexer as L
import qualified Lambda.Calculus as C
}

%name parse
%tokentype { (Int, Int, String, L.Token) }
%error {
  (\x ->
    case x of
      (line, col, str, token):_ ->
        error ("Unexpected " ++ (show token) ++ " at " ++
          (show line) ++ ":" ++ (show col))
      [] ->
        error "Unexpected end of file")
}

%token
  let        { (_, _, _, L.TokenLet) }
  in         { (_, _, _, L.TokenIn) }
  true       { (_, _, _, L.TokenTrue) }
  false      { (_, _, _, L.TokenFalse) }
  if         { (_, _, _, L.TokenIf) }
  then       { (_, _, _, L.TokenThen) }
  else       { (_, _, _, L.TokenElse) }
  lambda     { (_, _, _, L.TokenLambda) }
  '('        { (_, _, _, L.TokenLParen) }
  ')'        { (_, _, _, L.TokenRParen) }
  ','        { (_, _, _, L.TokenComma) }
  '='        { (_, _, _, L.TokenEquals) }
  '.'        { (_, _, _, L.TokenDot) }
  '+'        { (_, _, _, L.TokenPlus) }
  '-'        { (_, _, _, L.TokenMinus) }
  '*'        { (_, _, _, L.TokenTimes) }
  '/'        { (_, _, _, L.TokenDiv) }
  '<'        { (_, _, _, L.TokenLess) }
  '>'        { (_, _, _, L.TokenMore) }
  identifier { (_, _, $$, L.TokenIdentifier) }
  number     { (_, _, $$, L.TokenNumber) }

%nonassoc '<' '=' '>'
%left '+' '-'
%left '*' '/'

%expect 15

%%

Unit: Operation { $1 }

Operation: Operation '+' Operation { C.Operation C.Sum $1 $3 }
         | Operation '-' Operation { C.Operation C.Sub $1 $3 }
         | Operation '*' Operation { C.Operation C.Mul $1 $3 }
         | Operation '/' Operation { C.Operation C.Div $1 $3 }
         | Operation '<' Operation { C.Operation C.Lt $1 $3 }
         | Operation '>' Operation { C.Operation C.Gt $1 $3 }
         | Operation '=' Operation { C.Operation C.Eq $1 $3 }
         | Application { $1 }

Application: Application Expr     { C.Application $1 $2 }
           | Expr                 { $1 }

Expr: identifier    { C.Free $1 }
    | number        { C.Number (read $1) }
    | true          { C.True }
    | false         { C.False }
    | '(' Tuple ')' { $2 }
    | Let           { $1 }
    | Lambda        { $1 }
    | IfThenElse    { $1 }
    | '(' ')'       { C.UnitValue }

Tuple: Unit ',' Tuple { C.Pack $1 $3 }
     | Unit           { $1 }

Let: let identifier '=' Unit in Unit { C.Let $2 $4 $6 }

Lambda: lambda ParamList '.' Unit { $2 $4 }

IfThenElse: if Unit then Unit else Unit { C.If $2 $4 $6 }

ParamList: identifier           { C.Lambda $1 }
         | identifier ParamList { C.Lambda $1 . $2 }
