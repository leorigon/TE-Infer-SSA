module Lambda.Calculus where

import Debug.Trace
import qualified Data.Set as S
import qualified Data.Map as M

data Expr = Free String
          | Number Int
          | Text String
          | UnitValue
          | True
          | False
          | Pack Expr Expr
          | Let String Expr Expr
          | Lambda String Expr
          | If Expr Expr Expr
          | Application Expr Expr
          | Operation Operator Expr Expr

data Operator = Sum
              | Sub
              | Mul
              | Div
              | Lt
              | Gt
              | Eq

data Type = Int
          | Bool
          | String
          | Unit
          | Generic String
          | Arrow Type Type Type
          | Pair Type Type
       -- Effects:
          | Console
          | Foo
          | Bar
          | Pure
          -- O código não está verificando, MAS:
          -- O segundo elemento _precisa_ ser 1) outro Row, 2) Pure, ou
          --   3) Generic... se for um efeito (e.g., Console) pode dar ruim,
          --   eu acho; além disso, o primeiro elemento não deve ser outra row
          | Row Effect Effect
          deriving (Ord, Eq)

type Effect = Type

data Scheme = Forall [String] Type

class Substitutable a where
  ftv :: a -> S.Set String
  subst :: Subst -> a -> a

instance Substitutable Type where
  ftv (Int) = S.empty
  ftv (Bool) = S.empty
  ftv (String) = S.empty
  ftv (Unit) = S.empty
  ftv (Generic s) = S.singleton s
  ftv (Arrow a e b) = ftv a `S.union` ftv e `S.union` ftv b
  ftv (Pair a b) = ftv a `S.union` ftv b
  ftv (Pure) = S.empty
  ftv (Row head tail) = ftv head `S.union` ftv tail
  ftv (Console) = S.empty
  ftv (Foo) = S.empty
  ftv (Bar) = S.empty
  subst _ (Int) = Int
  subst _ (Bool) = Bool
  subst _ (String) = String
  subst _ (Unit) = Unit
  subst m (Generic s) = case M.lookup s m of
                          Nothing -> Generic s
                          Just t -> t
  subst m (Arrow a e b) = Arrow (subst m a) (subst m e) (subst m b)
  subst m (Pair a b) = Pair (subst m a) (subst m b)
  subst _ (Pure) = Pure
  subst m (Row head tail) = Row (subst m head) (subst m tail)
  subst _ (Console) = Console
  subst _ (Foo) = Foo
  subst _ (Bar) = Bar

instance Substitutable Scheme where
  ftv (Forall vars t) = (ftv t) `S.difference` (S.fromList vars)
  subst m (Forall vars t) = Forall vars (subst (foldr M.delete m vars) t)

instance Substitutable a => Substitutable [a] where
  ftv a = foldr S.union S.empty (fmap ftv a)
  subst m a = fmap (subst m) a

type Subst = M.Map String Type

a `compose` b = (M.map (subst a) b) `M.union` a

data Environment = Environment (M.Map String Scheme)
                 deriving Show

remove (Environment g) var = Environment (M.delete var g)

instance Substitutable Environment where
  ftv (Environment g) = ftv (M.elems g)
  subst m (Environment g) = Environment (M.map (subst m) g)

instance Show Expr where
  show =
    buildExpr []
    where
      buildAExpr xs (Free s) =
        s
      buildAExpr xs (Number n) =
        show n
      buildAExpr xs (Lambda.Calculus.True) =
        "true"
      buildAExpr xs (Lambda.Calculus.False) =
        "false"
      buildAExpr xs (Pack a b@(Pack _ _)) =
        "(" ++ (show a) ++ ", " ++ (tail (show b))
      buildAExpr xs (Pack a b) =
        "(" ++ (show a) ++ ", " ++ (show b) ++ ")"
      buildAExpr xs (UnitValue) =
        "()"
      buildAExpr xs a =
        "(" ++ (buildExpr xs a) ++ ")"

      buildBExpr xs (Application a b) =
        (buildBExpr xs a) ++ " " ++ (buildAExpr xs b)
      buildBExpr xs a =
        buildAExpr xs a

      buildCExpr xs (Operation Mul a b) =
        (buildCExpr xs a) ++ " * " ++ (buildCExpr xs b)
      buildCExpr xs (Operation Div a b) =
        (buildCExpr xs a) ++ " / " ++ (buildCExpr xs b)
      buildCExpr xs a =
        buildBExpr xs a

      buildDExpr xs (Operation Sum a b) =
        (buildDExpr xs a) ++ " + " ++ (buildDExpr xs b)
      buildDExpr xs (Operation Sub a b) =
        (buildDExpr xs a) ++ " - " ++ (buildDExpr xs b)
      buildDExpr xs a =
        buildCExpr xs a

      buildEExpr xs (Operation Lt a b) =
        (buildDExpr xs a) ++ " < " ++ (buildDExpr xs b)
      buildEExpr xs (Operation Gt a b) =
        (buildDExpr xs a) ++ " > " ++ (buildDExpr xs b)
      buildEExpr xs (Operation Eq a b) =
        (buildDExpr xs a) ++ " = " ++ (buildDExpr xs b)
      buildEExpr xs a =
        buildDExpr xs a

      buildExpr xs (Lambda s b) =
        "λ" ++ s ++ "." ++ (buildExpr (s:xs) b)
      buildExpr xs (Let s a b) =
        "let " ++ s ++ " = " ++ (buildAExpr xs a) ++ " in " ++ (buildExpr (s:xs) b)
      buildExpr xs (If a b c) =
        "if " ++ (buildAExpr xs a) ++ " then " ++ (buildAExpr xs b) ++ " else " ++ (buildAExpr xs c)
      buildExpr xs a =
        buildEExpr xs a

instance Show Type where
  show (Int) =
    "int"
  show (Bool) =
    "bool"
  show (String) =
    "string"
  show (Unit) =
    "unit"
  show (Generic s) =
    s
  show (Arrow a@(Arrow _ _ _) e b) =
    "(" ++ (show a) ++ ") → " ++ (show e) ++ " " ++ (show b)
  show (Arrow a e b) =
    (show a) ++ " → " ++ (show e) ++ " " ++ (show b)
  show (Pair a b@(Pair _ _)) =
    "(" ++ (show a) ++ ", " ++ (tail (show b))
  show (Pair a b) =
    "(" ++ (show a) ++ ", " ++ (show b) ++ ")"
  show (Pure) =
    "pure"
  show (Row head tail) =
    -- TODO: better printing for this
    "<" ++ show head ++ " | " ++ show tail ++ ">"
  show (Console) =
    "console"
  show (Foo) =
    "foo"
  show (Bar) =
    "bar"

instance Show Scheme where
  show (Forall vars t) =
    if length vars > 0 then
      "∀" ++ (show vars) ++ "." ++ (show t)
    else
      show t
