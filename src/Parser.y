{
module Parser where

import Data.Char
import qualified Lexer as L
import qualified Data.Map.Lazy as M
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
  algorithm  { (_, _, _, L.TokenAlgorithm) }
  var        { (_, _, _, L.TokenVar) }
  int        { (_, _, _, L.TokenInt) }
  bool       { (_, _, _, L.TokenBool) }
  unit       { (_, _, _, L.TokenUnit) }
  string     { (_, _, _, L.TokenString) }
  if         { (_, _, _, L.TokenIf) }
  else       { (_, _, _, L.TokenElse) }
  while      { (_, _, _, L.TokenWhile) }
  for        { (_, _, _, L.TokenFor) }
  switch     { (_, _, _, L.TokenSwitch) }
  return     { (_, _, _, L.TokenReturn) }
  goto       { (_, _, _, L.TokenGoto) }
  case       { (_, _, _, L.TokenCase) }
  default    { (_, _, _, L.TokenDefault) }
  break      { (_, _, _, L.TokenBreak) }
  continue   { (_, _, _, L.TokenContinue) }
  ref        { (_, _, _, L.TokenRef) }
  identifier { (_, _, $$, L.TokenIdentifier) }
  number_lit { (_, _, $$, L.TokenNumberLiteral) }
  string_lit { (_, _, $$, L.TokenStringLiteral) }
  '('        { (_, _, _, L.TokenLeftParen) }
  ')'        { (_, _, _, L.TokenRightParen) }
  '{'        { (_, _, _, L.TokenLeftBrace) }
  '}'        { (_, _, _, L.TokenRightBrace) }
  '='        { (_, _, _, L.TokenAssign) }
  ';'        { (_, _, _, L.TokenSemicolon) }
  ':'        { (_, _, _, L.TokenColon) }
  ','        { (_, _, _, L.TokenComma) }
  '+'        { (_, _, _, L.TokenAdd) }
  '-'        { (_, _, _, L.TokenSub) }
  '*'        { (_, _, _, L.TokenMul) }
  '/'        { (_, _, _, L.TokenDiv) }
  '%'        { (_, _, _, L.TokenMod) }
  '<'        { (_, _, _, L.TokenLessThan) }
  '>'        { (_, _, _, L.TokenMoreThan) }
  '=='       { (_, _, _, L.TokenEquals) }
  '!='       { (_, _, _, L.TokenDiffs) }
  '++'       { (_, _, _, L.TokenIncr) }
  '--'       { (_, _, _, L.TokenDecr) }

%nonassoc THEN
%nonassoc else ref identifier number
%nonassoc '<' '>' '==' '!='
%left UNARY_MINUS UNARY_STAR
%left '+' '-'
%left '*' '/' '%'
%nonassoc '(' ')'

%expect 0

%%

Unit: ToplevelList                                  { $1 }

ToplevelList: {- Empty -}                           { [] }
            | Toplevel ToplevelList                 { $1 : $2 }

Toplevel: Algorithm                                 { $1 }

Algorithm: algorithm identifier ParamList Body      { Algorithm $2 $3 $4 }

ParamList: '(' DeclaratorListOpt ')'                { $2 }

DeclaratorListOpt: {- empty -}                      { [] }
                 | DeclaratorList                   { $1 }

DeclaratorList: Declarator                          { [$1] }
              | Declarator ',' DeclaratorList       { $1 : $3 }

Declarator: var identifier                          { DeclareVar $2 }
          | int identifier                          { DeclareInt $2 }
          | bool identifier                         { DeclareBool $2 }
          | string identifier                       { DeclareString $2 }

Body: '{' StatementSequenceOpt '}'                  { BlockStatement $2 }

StatementSequenceOpt: {- empty -}                   { EmptyStatement }
                    | StatementSequence             { $1 }

StatementSequence: Statement                        { $1 }
                 | Statement StatementSequence      { SequenceStatement $1 $2 }

Statement: AssignmentStatement                      { $1 }
         | CallStatement                            { $1 }
         | IfStatement                              { $1 }
         | WhileStatement                           { $1 }
         | ForStatement                             { $1 }
         | SwitchStatement                          { $1 }
         | ReturnStatement                          { $1 }
         | GotoStatement                            { $1 }
         | BreakStatement                           { $1 }
         | ContinueStatement                        { $1 }
         | DeclarationStatement                     { $1 }
         | LabeledStatement                         { $1 }

Assignment: identifier '=' Expression               { ($1, $3) }
          | identifier '++'                         { ($1, AddExpression (VarExpression $1) (NumExpression 1)) }
          | identifier '--'                         { ($1, AddExpression (VarExpression $1) (NumExpression 1)) }

AssignmentStatement: Assignment ';'                 { AssignmentStatement (fst $1) (snd $1) }

CallStatement: identifier ArgumentList ';'          { CallStatement $1 $2 }

ArgumentList: '(' ExpressionListOpt ')'             { $2 }

ExpressionListOpt: {- empty -}                      { [] }
                 | ExpressionList                   { $1 }

ExpressionList: Expression                          { [$1] }
              | Expression ',' ExpressionList       { $1 : $3 }

IfStatement: IfClause ElseStatement                 { $1 $2 }

ElseStatement: else Body                            { $2 }
             | else Statement                       { $2 }
             | {- empty -} %prec THEN               { EmptyStatement }

IfClause: if '(' Expression ')' Body                { IfStatement $3 $5 }
        | if '(' Expression ')' Statement           { IfStatement $3 $5 }

WhileStatement: while '(' Expression ')' Body       { WhileStatement $3 $5 }
              | while '(' Expression ')' Statement  { WhileStatement $3 $5 }

ForStatement: for '(' DeclarationStatement
                Expression ';' Assignment ')' Body  { ForStatement $3 $4 (fst $6) (snd $6) $8 }
            | for '(' AssignmentStatement
                Expression ';' Assignment ')' Body  { ForStatement $3 $4 (fst $6) (snd $6) $8 }
            | for '(' DeclarationStatement
                Expression ';' Assignment ')'
                Statement                           { ForStatement $3 $4 (fst $6) (snd $6) $8 }
            | for '(' AssignmentStatement
                Expression ';' Assignment ')'
                Statement                           { ForStatement $3 $4 (fst $6) (snd $6) $8 }

SwitchStatement: switch '(' Expression ')' Body     { SwitchStatement $3 $5 }

ReturnStatement: return Expression ';'              { ReturnStatement $2 }
               | return ';'                         { ReturnStatement UnitExpression }

GotoStatement: goto identifier ';'                  { GotoStatement $2 }

BreakStatement: break ';'                           { BreakStatement }

ContinueStatement: continue ';'                     { ContinueStatement }

DeclarationStatement: Declarator ';'                { DeclarationStatement $1 Nothing }
                    | Declarator '=' Expression ';' { DeclarationStatement $1 (Just $3) }

LabeledStatement: identifier ':' Statement          { LabeledStatement $1 $3 }
                | case number_lit ':' Statement     { CaseStatement (read $2) $4 }
                | default ':' Statement             { DefaultStatement $3 }

Expression: identifier                              { VarExpression $1 }
          | number_lit                              { NumExpression (read $1) }
          | string_lit                              { StrExpression $1 }
          | identifier ArgumentList                 { CallExpression $1 $2 }
          | Expression '+' Expression               { AddExpression $1 $3 }
          | Expression '-' Expression               { SubExpression $1 $3 }
          | Expression '*' Expression               { MulExpression $1 $3 }
          | Expression '/' Expression               { DivExpression $1 $3 }
          | Expression '%' Expression               { ModExpression $1 $3 }
          | Expression '<' Expression               { LessThanExpression $1 $3 }
          | Expression '>' Expression               { MoreThanExpression $1 $3 }
          | Expression '==' Expression              { EqualsExpression $1 $3 }
          | Expression '!=' Expression              { DiffsExpression $1 $3 }
          | ref Expression                          { RefExpression $2 }
          | '*' Expression %prec UNARY_STAR         { DerefExpression $2 }
          | '-' Expression %prec UNARY_MINUS        { NegExpression $2 }
          | '(' ')'                                 { UnitExpression }
          | '(' Expression ')'                      { $2 }

{
type Identifier = String

data Toplevel = Algorithm Identifier Parameters Statement
              deriving Show

type Parameters = [Declarator]

data Declarator = DeclareVar Identifier
                | DeclareInt Identifier
                | DeclareBool Identifier
                | DeclareString Identifier

getDeclaratorName (DeclareVar x) = x
getDeclaratorName (DeclareInt x) = x
getDeclaratorName (DeclareBool x) = x
getDeclaratorName (DeclareString x) = x

instance Show Declarator where
  show (DeclareVar x) =
    "var " ++ x
  show (DeclareInt x) =
    "int " ++ x
  show (DeclareBool x) =
    "bool " ++ x
  show (DeclareString x) =
    "string " ++ x

data Statement = EmptyStatement
               | BlockStatement Statement
               | AssignmentStatement Identifier Expression
               | CallStatement Identifier Arguments
               | IfStatement Expression Statement Statement
               | WhileStatement Expression Statement
               | ForStatement Statement Expression Identifier Expression Statement
               | SwitchStatement Expression Statement
               | ReturnStatement Expression
               | GotoStatement Identifier
               | BreakStatement
               | ContinueStatement
               | DeclarationStatement Declarator (Maybe Expression)
               | CaseStatement Int Statement
               | DefaultStatement Statement
               | LabeledStatement Identifier Statement
               | SequenceStatement Statement Statement
               deriving Show

type Arguments = [Expression]

data Expression = VarExpression Identifier
                | IndexedVarExpression Identifier Int
                | NumExpression Int
                | StrExpression String
                | CallExpression Identifier Arguments
                | AddExpression Expression Expression
                | SubExpression Expression Expression
                | MulExpression Expression Expression
                | DivExpression Expression Expression
                | ModExpression Expression Expression
                | LessThanExpression Expression Expression
                | MoreThanExpression Expression Expression
                | EqualsExpression Expression Expression
                | DiffsExpression Expression Expression
                | RefExpression Expression
                | DerefExpression Expression
                | NegExpression Expression
                | UnitExpression

instance Show Expression where
  show (VarExpression x) =
    x
  show (IndexedVarExpression x n) =
    let subscript = chr . (+) 0x2050 . ord in
    x ++ map subscript (show n)
  show (NumExpression n) =
    show n
  show (StrExpression s) =
    concat (map (\s -> case s of { '"' -> "\\\""; c -> [c] }) s)
  show (CallExpression fun args) =
    "(" ++ fun ++ concat (map ((++) " " . show) args) ++ ")"
  show (AddExpression left right) =
    "(+ " ++ show left ++ " " ++ show right ++ ")"
  show (SubExpression left right) =
    "(- " ++ show left ++ " " ++ show right ++ ")"
  show (MulExpression left right) =
    "(* " ++ show left ++ " " ++ show right ++ ")"
  show (DivExpression left right) =
    "(/ " ++ show left ++ " " ++ show right ++ ")"
  show (ModExpression left right) =
    "(+ " ++ show left ++ " " ++ show right ++ ")"
  show (LessThanExpression left right) =
    "(< " ++ show left ++ " " ++ show right ++ ")"
  show (MoreThanExpression left right) =
    "(> " ++ show left ++ " " ++ show right ++ ")"
  show (EqualsExpression left right) =
    "(== " ++ show left ++ " " ++ show right ++ ")"
  show (DiffsExpression left right) =
    "(!= " ++ show left ++ " " ++ show right ++ ")"
  show (RefExpression arg) =
    "(& " ++ show arg ++ ")"
  show (DerefExpression arg) =
    "(@ " ++ show arg ++ ")"
  show (UnitExpression) =
    "()"

setVariablesIndexes expr scope =
  recurse expr
  where
    recurse expr =
      case expr of
        VarExpression var ->
          case M.lookup var scope of
            Just i -> IndexedVarExpression var i
            Nothing -> error $ "Use of undeclared var `" ++ var ++ "`"
        IndexedVarExpression var _ ->
          case M.lookup var scope of
            Just i -> IndexedVarExpression var i
            Nothing -> error $ "Use of undeclared var `" ++ var ++ "`"
        NumExpression _ ->
          expr
        StrExpression _ ->
          expr
        CallExpression fun args ->
          CallExpression fun (map recurse args)
        AddExpression left right ->
          AddExpression (recurse left) (recurse right)
        SubExpression left right ->
          SubExpression (recurse left) (recurse right)
        MulExpression left right ->
          MulExpression (recurse left) (recurse right)
        DivExpression left right ->
          DivExpression (recurse left) (recurse right)
        ModExpression left right ->
          ModExpression (recurse left) (recurse right)
        LessThanExpression left right ->
          LessThanExpression (recurse left) (recurse right)
        MoreThanExpression left right ->
          MoreThanExpression (recurse left) (recurse right)
        EqualsExpression left right ->
          EqualsExpression (recurse left) (recurse right)
        DiffsExpression left right ->
          DiffsExpression (recurse left) (recurse right)
        RefExpression arg ->
          RefExpression (recurse arg)
        DerefExpression arg ->
          DerefExpression (recurse arg)
        NegExpression arg ->
          NegExpression (recurse arg)
        UnitExpression ->
          expr
}
