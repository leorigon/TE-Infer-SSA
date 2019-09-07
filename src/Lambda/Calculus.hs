{-# LANGUAGE FlexibleContexts #-}
module Lambda.Calculus where

import Data.List
import Control.Monad.RWS
import qualified Data.Set as S
import qualified Data.Map as M
import Debug.Trace

data Expr = Free String
          | Number Int
          | Text String
          | UnitValue
          | TrueValue
          | FalseValue
          | Let String Expr Expr
          | Lambda String Expr
          | If Expr Expr Expr
          | Application Expr Expr
          | Operation Operator Expr Expr
          | Where [(String, Expr)] Expr
          | Handler String [(Maybe String, Expr)] Expr

-- TODO: Change it for Application.
data Operator = Sum
              | Sub
              | Mul
              | Div
              | Lt
              | Gt
              | Eq
              | EqEq

data Type = Int
          | Bool
          | String
          | Unit
          | Generic String
          | Arrow Type Type Type
          | Constant String [Type]
          | Ref Type
          | Console
          | Foo
          | Bar
          | Pure
          | State
          | Row Effect Effect
          | Computation Type Effect
          deriving (Ord, Eq)

type Effect = Type

data Scheme = Forall [String] Type
            deriving Eq

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
    ftv (Ref a) = ftv a
    ftv (Pure) = S.empty
    ftv (Row head tail) = ftv head `S.union` ftv tail
    ftv (Computation t k) = ftv t `S.union` ftv k
    ftv (Console) = S.empty
    ftv (Foo) = S.empty
    ftv (Bar) = S.empty
    ftv (State) = S.empty
    ftv (Constant _ args) = foldl S.union S.empty (fmap ftv args)
    subst _ (Int) = Int
    subst _ (Bool) = Bool
    subst _ (String) = String
    subst _ (Unit) = Unit
    subst m (Generic s) = case M.lookup s m of
                            Nothing -> Generic s
                            Just t -> t
    subst m (Arrow a e b) = Arrow (subst m a) (subst m e) (subst m b)
    subst m (Ref a) = Ref (subst m a)
    subst _ (Pure) = Pure
    subst m (Row head tail) = Row (subst m head) (subst m tail)
    subst m (Computation t k) = Computation (subst m t) (subst m k)
    subst _ (Console) = Console
    subst _ (Foo) = Foo
    subst _ (Bar) = Bar
    subst _ (State) = State
    subst m (Constant k args) = Constant k (fmap (subst m) args)

instance Substitutable Scheme where
    ftv (Forall vars t) = (ftv t) `S.difference` (S.fromList vars)
    subst m (Forall vars t) = Forall vars (subst (foldr M.delete m vars) t)

instance Substitutable a => Substitutable [a] where
    ftv a = foldr S.union S.empty (fmap ftv a)
    subst m a = fmap (subst m) a

type Subst = M.Map String Type

newtype Environment = Environment { getEnvironment :: M.Map String Scheme}
                    deriving Eq
                    
instance Show Environment where
  show (Environment map) =
    init $ unlines $ fmap (\(key, value) -> key ++ ": " ++ show value) (M.toList map)

instance Substitutable Environment where
    ftv (Environment g) = ftv (M.elems g)
    subst m (Environment g) = Environment (M.map (subst m) g)

instance Show Type where
    show (Int) = "int"
    show (Bool) = "bool"
    show (String) = "string"
    show (Unit) = "unit"
    show (Generic s) = s
    show (Constant s []) = s
    show (Constant s args) = 
        s ++ "<" ++ intercalate ", " (fmap show args) ++ ">"
    show (Arrow a@(Arrow _ _ _) e b) =
        "(" ++ (show a) ++ ") → " ++ (show e) ++ " " ++ (show b)
    show (Arrow a e b) =
        (show a) ++ " → " ++ (show e) ++ " " ++ (show b)
    show (Ref a) = "ref<" ++ show a ++ ">"
    show (Pure) = "pure"
    show (Row e es@(Row _ _)) =
        "<" ++ show e ++ ", " ++ tail (show es)
    show (Row e Pure) =
        "<" ++ show e ++ ">"
    show (Row e es) =
        "<" ++ show e ++ ", " ++ show es ++ ">"
    show (Computation t k) =
        show t ++ " ! " ++ show k
    show (State) = "st"
    show (Console) = "console"
    show (Foo) = "foo"
    show (Bar) = "bar"

instance Show Scheme where
    show (Forall vars t) =
      if length vars > 0 then
        "∀" ++ intercalate " " vars ++ "." ++ (show t)
      else show t

instance Show Expr where
    show expr =
        let (_, _, w) = runRWS (worker expr) () (0, 0) in w
        where
            worker (Free s) = do
                emit s
            worker (Number n) = do
                emit (show n)
            worker (Text s) = do
                emit (show s)
            worker (UnitValue) = do
                emit "()"
            worker (TrueValue) = do
                emit "true"
            worker (FalseValue) = do
                emit "false"
            worker (Let s a b) = do
                error "TODO: let"
            worker lambda@(Lambda _ _) = do
                emit "\\"
                emitLambda lambda
                
            worker (If e a b) = do
                i <- getIndentation
                emit "if"
                saveIndentation
                emit " "
                worker e
                newline
                indent
                emit "then "
                worker a
                newline
                indent
                emit "else "
                worker b
                putIndentation i

            worker (Application lambda@(Lambda s b) a) = do
                i <- getIndentation
                saveIndentation
                emit "let "
                emit s
                emit " = "
                worker a
                emit " in"
                newline
                indent
                worker b
                putIndentation i

            worker (Application a b) = do
                emit "("
                worker a
                emit " "
                worker b
                emit ")"

            worker (Operation op a b) = do
                worker a
                emit $ case op of
                    Lambda.Calculus.Sum -> " + "
                    Lambda.Calculus.Sub -> " - "
                    Lambda.Calculus.Mul -> " * "
                    Lambda.Calculus.Div -> " / "
                    Lambda.Calculus.Lt -> " < "
                    Lambda.Calculus.Gt -> " > "
                    Lambda.Calculus.Eq -> " == "
                worker b

            worker (Where bindings e) = do
                saveIndentation
                i <- getIndentation
                emit "let "
                saveIndentation
                emitBindings bindings
                putIndentation i
                indent
                emit "in "
                worker e

            emit str = do
                (a, b) <- get
                tell str
                put (a + length str, b)

            newline = do
                tell "\n"
                (_, b) <- get
                put (0, b)

            getIndentation = do
                (_, b) <- get
                return b
            
            putIndentation b = do
                (a, _) <- get
                put (a, b)
            
            saveIndentation = do
                (a, _) <- get
                putIndentation a
            
            indent = do
                (a, b) <- get
                if a /= 0 then error "We Screwed up identation"
                else emit (replicate b ' ')
            
            emitLambda (Lambda s child@(Lambda _ _)) = do
                emit s
                emit " "
                emitLambda child
            
            emitLambda (Lambda s child) = do
                i <- getIndentation
                emit s
                emit " ->"
                newline
                indent
                emit "  "
                saveIndentation
                worker child
                putIndentation i

            emitBindings ((s, e):rest) = do
                i <- getIndentation
                saveIndentation
                emit s
                emit " "
                emitSingleBinding e
                newline
                when (length rest /= 0) $ do
                    indent
                    emitBindings rest
                putIndentation i
      
            emitBindings [] = do
                return ()

            emitSingleBinding (Lambda s e) = do
                emit s
                emit " "
                emitSingleBinding e
      
            emitSingleBinding e = do
                i <- getIndentation
                emit "="
                newline
                indent
                emit "  "
                worker e
                putIndentation i

remove :: Environment -> String -> Environment
remove (Environment g) var = Environment (M.delete var g)

infixr 4 @@
(@@) :: Subst -> M.Map String Type -> M.Map String Type
a @@ b = (M.map (subst a) b) `M.union` a

extend env s a =
    let (Environment env') = remove env s in
        Environment (env' `M.union` (M.singleton s a))
      
extend' env s a =
    let (Environment env') = remove env s in
    Environment (env' `M.union` (M.singleton s (Forall [] a)))

rowsEquiv :: Effect -> Effect -> Bool
rowsEquiv epsilon1 epsilon2 =
    toSet epsilon1 == toSet epsilon2
    where
        toSet (Row l e) =
            S.singleton l `S.union` toSet e
        toSet e@(Generic _) = S.singleton e
