{-# LANGUAGE FlexibleContexts #-}
module Lambda.Inference where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Identity
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Lambda.Calculus as C
import Debug.Trace

data TypeError = CannotUnify C.Type C.Type
               | InfiniteType String C.Type
               | UnboundVariable String
               | Inside C.Expr TypeError
               deriving Show

type InfererT m a = ExceptT TypeError (ReaderT () (StateT Int m)) a

runInferer' i = do
    (res, _) <- runStateT (runReaderT (runExceptT i) ()) 0
    return res

newTypeVar = do
  s <- get
  modify (+1)
  return $ C.Generic (letters !! s)
  where
    letters = [1..] >>= flip replicateM ['a'..'z']

generalize g t =
    C.Forall vars t
    where
        vars = S.toList ((C.ftv t) `S.difference` (C.ftv g))

instantiate (C.Forall vars t) = do
    nvars <- mapM (const $ newTypeVar) vars
    let m = M.fromList (zip vars nvars)
    return $ C.subst m t

unify (C.Arrow a e b) (C.Arrow x f y) = do
    s1 <- unify a x
    s2 <- unify (C.subst s1 e) (C.subst s1 f)
    s3 <- unify (C.subst (s2 `C.compose` s1) b) (C.subst (s2 `C.compose` s1) y)
    return $ s3 `C.compose` s2 `C.compose` s1
unify (C.Pair a b) (C.Pair x y) = do
    --s1 <- unify a x
    --s2 <- unify (C.subst s1 b) (C.subst s1 y)
    --return $ s1 `C.compose` s2
    error "TODO: UNIFY PAIRS"
unify (C.Generic a) t = do
    varBind a t
unify t (C.Generic a) = do
    varBind a t
unify C.Int C.Int = do
   return M.empty
unify C.Bool C.Bool = do
    return M.empty
unify C.Pure C.Pure = do
    return M.empty
unify C.Console C.Console = do
    return M.empty
unify C.Foo C.Foo = do
    return M.empty
unify C.Bar C.Bar = do
    return M.empty
unify a@(C.Row l k1) k2 = do
    (k3, s1) <- unifyRow k2 l
    -- TODO: CHECK THAT tl(k1) NOT IN dom(s1)
    --       OTHERWISE FAIL
    -- IMPORTANT!!! OTHERWISE COULD END UP IN INFINITE LOOP
    s2 <- unify (C.subst s1 k1) (C.subst s1 k3)
    return $ s2 `C.compose` s1
unify a b = do
    throwError $ CannotUnify a b

-- FROM: https://arxiv.org/pdf/1406.2061.pdf
unifyRow (C.Row l' k) l =
    -- EFF-HEAD
    if l == l' then do
        s <- unify l l'
        return (k, s)
    -- EFF-SWAP
    else do
        (k', s) <- unifyRow k l
        return (C.Row l k', s)
unifyRow (C.Generic mi) l = do
    -- EFF-TAIL
    mi' <- newTypeVar
    return (mi', M.singleton mi (C.Row l mi'))
unifyRow a b =
    throwError $ CannotUnify a b

varBind a t | t == C.Generic a =
                return M.empty
            | a `S.member` C.ftv t =
                throwError $ InfiniteType a t
            | otherwise =
                return $ M.singleton a t

infer :: C.Environment -> C.Expr -> ExceptT TypeError (ReaderT () (StateT Int Identity)) (C.Subst, C.Type, C.Effect)

infer (C.Environment env) (C.Free s) =
    case M.lookup s env of
        Just sigma -> do
            t <- instantiate sigma
            mi <- newTypeVar
            return (M.empty, t, mi)
        Nothing ->
            throwError $ UnboundVariable s
infer _ (C.Number _) = do
    mi <- newTypeVar
    return (M.empty, C.Int, mi)
infer _ (C.Text _) = do
    mi <- newTypeVar
    return (M.empty, C.String, mi)
infer _ (C.UnitValue) = do
    mi <- newTypeVar
    return (M.empty, C.Unit, mi)
infer _ (C.True) = do
    mi <- newTypeVar
    return (M.empty, C.Bool, mi)
infer _ (C.False) = do
    mi <- newTypeVar
    return (M.empty, C.Bool, mi)
infer env (C.Pack e1 e2) = do
    --(s1, t1, _) <- infer env e1
    --(s2, t2, _) <- infer (C.subst s1 env) e2
    --return (s1 `C.compose` s2, C.Pair (C.subst s2 t1) t2, error "TODO: effect")
    error "TODO: implement infer for tuples"
infer env (C.Lambda s e) = do
    tv <- newTypeVar
    let (C.Environment env') = C.remove env s
    let env'' = C.Environment (env' `M.union` (M.singleton s (C.Forall [] tv)))
    (s1, t1, k1) <- infer env'' e
    mi <- newTypeVar
    return (s1, C.Arrow (C.subst s1 tv) k1 t1, mi)
infer env expr@(C.Application e1 e2) = do
    tv <- newTypeVar
    (s1, t1, k1) <- infer env e1
    (s2, t2, k2) <- infer (C.subst s1 env) e2
    s3 <- unify (C.subst s2 t1) (C.Arrow t2 k2 tv)
    let foo = (C.subst (s3 `C.compose` s2) k1)
    let bar = (C.subst s3 k2)
    s4 <- unify (C.subst (s3 `C.compose` s2) k1) (C.subst s3 k2)
    return (s4 `C.compose` s3 `C.compose` s2 `C.compose` s1,
            C.subst (s4 `C.compose` s3) tv,
            C.subst (s4 `C.compose` s3) k2)

    `catchError`
    \e ->
        throwError $ Inside expr e
infer env (C.Let x e1 e2) = do
    (s1, t1, k1) <- infer env e1
    let C.Environment env' = C.remove env x
    let t' = generalize (C.subst s1 env) t1
    let env'' = C.Environment (M.insert x t' env')
    -- Vale notar: Koka exige que o valor do let seja puro
    -- Isso está correto?
    s2 <- unify k1 C.Pure
    (s3, t2, k2) <- infer (C.subst (s2 `C.compose` s1) env'') e2
    return (s3 `C.compose` s2 `C.compose` s1, t2, k2)

infer env (C.Operation C.Sum a b) = do
    infer env (C.Application (C.Application (C.Free "(+)") a) b)
infer env (C.Operation C.Sub a b) = do
    infer env (C.Application (C.Application (C.Free "(-)") a) b)
infer env (C.Operation C.Mul a b) = do
    infer env (C.Application (C.Application (C.Free "(*)") a) b)
infer env (C.Operation C.Div a b) = do
    infer env (C.Application (C.Application (C.Free "(/)") a) b)
infer env (C.Operation C.Lt a b) = do
    infer env (C.Application (C.Application (C.Free "(<)") a) b)
infer env (C.Operation C.Gt a b) = do
    infer env (C.Application (C.Application (C.Free "(>)") a) b)
infer env (C.Operation C.Eq a b) = do
    infer env (C.Application (C.Application (C.Free "(=)") a) b)
infer env (C.If a b c) = do
    infer env (C.Application (C.Application (C.Application (C.Free "(?:)") a) b) c)

my_env =
    C.Environment (M.fromList [
        ("print", C.Forall ["a", "u"] $ C.Arrow (C.Generic "a") (C.Row C.Console $ C.Generic "u") C.Unit),
        ("foo", C.Forall ["u"] $ C.Arrow C.Int (C.Row C.Foo $ C.Generic "u") C.Int),
        ("bar", C.Forall ["u"] $ C.Arrow C.Int (C.Row C.Bar $ C.Generic "u") C.Int),
        -- Exemplo de como podemos remover um efeito de uma closure :)
        --("removeFoo",
        --    C.Forall ["a", "b", "u"] $
        --        C.Arrow
        --            (C.Arrow (C.Generic "a") (C.Row C.Foo (C.Generic "u")) (C.Generic "a"))
        --            (C.Pure)
        --            (C.Arrow (C.Generic "a") (C.Generic "u") (C.Generic "a")))

    --    ("fix", C.Forall ["'a"] $
    --      C.Arrow (C.Arrow (C.Generic "'a") (C.Generic "'a")) (C.Generic "'a")),
        ("(+)", C.Forall ["a", "b"] $ C.Arrow C.Int (C.Generic "a")
            (C.Arrow C.Int (C.Generic "b") C.Int)),
        ("(-)", C.Forall ["a", "b"] $ C.Arrow C.Int (C.Generic "a")
            (C.Arrow C.Int (C.Generic "b") C.Int)),
        ("(*)", C.Forall ["a", "b"] $ C.Arrow C.Int (C.Generic "a")
            (C.Arrow C.Int (C.Generic "b") C.Int)),
        ("(/)", C.Forall ["a", "b"] $ C.Arrow C.Int (C.Generic "a")
            (C.Arrow C.Int (C.Generic "b") C.Int)),
        ("(<)", C.Forall ["a", "b"] $ C.Arrow C.Int (C.Generic "a")
            (C.Arrow C.Int (C.Generic "b") C.Bool)),
        ("(>)", C.Forall ["a", "b"] $ C.Arrow C.Int (C.Generic "a")
            (C.Arrow C.Int (C.Generic "b") C.Bool)),
        ("(=)", C.Forall ["a", "b"] $ C.Arrow C.Int (C.Generic "a")
            (C.Arrow C.Int (C.Generic "b") C.Bool))
        -- TODO: (?:) para if statement
    ])

runInferer :: C.Expr -> Either TypeError C.Type
runInferer e =
    runIdentity runInfererM
    where
        runInfererM =
            runInferer' $ do
                (s, t, k) <- infer my_env e
                put 0
                instantiate $ generalize my_env (C.subst s t)
