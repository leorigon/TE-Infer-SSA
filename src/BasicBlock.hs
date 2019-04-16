{-# LANGUAGE RecursiveDo #-}
module BasicBlock where

import qualified Parser as P
import qualified Data.Map.Lazy as M
import Control.Monad.State.Lazy
import Debug.Trace

type Label = Int

data Command = CommandCall String P.Arguments
             | CommandAssign String Int P.Expression
             | CommandDecl P.Declarator

instance Show Command where
    show (CommandCall fun args) =
        show (P.CallExpression fun args)
    show (CommandAssign var level expr) =
        show (P.IndexedVarExpression var level) ++ " = " ++ show expr
    show (CommandDecl decl) =
        show [decl]

data Node = Entry P.Parameters Label
          | Leave Label P.Expression
          | Jmp Label Command Label
          | Ift Label P.Expression Label Label
          deriving Show

make_label = do
    (label, break, continue, scope, current_scope, counter) <- get
    put (label + 1, break, continue, scope, current_scope, counter)
    return label

make_counter = do
    (label, break, continue, scope, current_scope, counter) <- get
    put (label, break, continue, scope, current_scope, counter + 1)
    return counter

get_break :: State (a, b, c, d, e, f) b
get_break = do
    (_, break, _, _, _, _) <- get
    return break

put_break :: b -> State (a, b, c, d, e, f) ()
put_break break = do
    (label, _, continue, scope, current_scope, counter) <- get
    put (label, break, continue, scope, current_scope, counter)

get_continue :: State (a, b, c, d, e, f) c
get_continue = do
    (_, _, continue, _, _, _) <- get
    return continue

put_continue :: c -> State (a, b, c, d, e, f) ()
put_continue continue = do
    (label, break, _, scope, current_scope, counter) <- get
    put (label, break, continue, scope, current_scope, counter)

get_scope :: State (a, b, c, d, e, f) d
get_scope = do
    (_, _, _, scope, _, _) <- get
    return scope

put_scope :: d -> State (a, b, c, d, e, f) ()
put_scope scope = do
    (label, break, continue, _, current_scope, counter) <- get
    put (label, break, continue, scope, current_scope, counter)

get_current_scope :: State (a, b, c, d, e, f) e
get_current_scope = do
    (_, _, _, _, current_scope, _) <- get
    return current_scope

put_current_scope :: e -> State (a, b, c, d, e, f) ()
put_current_scope current_scope = do
    (label, break, continue, scope, _, counter) <- get
    put (label, break, continue, scope, current_scope, counter)

assignVariable :: String -> P.Expression -> State (a, b, c, M.Map String Int, e, f) Command
assignVariable var expr = do
    scope <- get_scope
    let level = case M.lookup var scope of
                    Just i -> i
                    Nothing -> error $ "Use of undeclared var `" ++ var ++ "`"
    expr' <- annotateExpression expr
    return $ CommandAssign var level expr'

declareVariable decl = do
    scope <- get_scope
    current_scope <- get_current_scope
    let name = P.getDeclaratorName decl
    put_scope $ M.insert name current_scope scope
    return name

push_scope = do
    old_current_scope <- get_current_scope
    counter <- make_counter
    put_current_scope counter
    old_scope <- get_scope
    return (old_scope, old_current_scope)

restore_scope (old_scope, old_current_scope) = do
    put_scope old_scope
    put_current_scope old_current_scope

annotateExpression :: P.Expression -> State (a, b, c, M.Map String Int, e, f) P.Expression
annotateExpression expr = do
    scope <- get_scope
    return $ P.setVariablesIndexes expr scope

astToNodes stmt parameters =
    -- Trick: "tying the knot"; since we never use the destination label of
    -- blocks while building them, we can use their return map inside the goto
    -- function, lazily, so we don't need to check the program tree twice! :D
    let fake_label = error "invalid continue/break!"
        initial_scope = M.fromList $ map (flip (,) 0 . P.getDeclaratorName) parameters
        initial_state = (2, fake_label, fake_label, initial_scope, 0, 1)
        (first_label, (label_map, _), result) = evalState (go (M.empty, M.empty) stmt 0) initial_state
        goto name =
            case M.lookup name label_map of
                Just label -> do
                    label
                Nothing -> do
                   error $ "attempting to goto to unknown label `" ++ name ++ "`"
        go m stmt final =
            case stmt of
                P.EmptyStatement -> do
                    return (final, m, [])
                P.BlockStatement stmt -> do
                    (old_scope, old_current_scope) <- push_scope
                    res <- go m stmt final
                    restore_scope (old_scope, old_current_scope)
                    return res
                P.CallStatement fun args -> do
                    label <- make_label
                    args' <- mapM annotateExpression args
                    return (label, m, [Jmp label (CommandCall fun args') final])
                P.AssignmentStatement var expr -> do
                    label <- make_label
                    assignment <- assignVariable var expr
                    return (label, m, [Jmp label assignment final])
                P.SequenceStatement first second -> do
                    rec (first_label, m', res1) <- go m first second_label
                        (second_label, m'', res2) <- go m' second final
                    return (first_label, m'', res1 ++ res2)
                P.IfStatement expr success failure -> do
                    label <- make_label
                    (success_label, m', res1) <- go m success final
                    (failure_label, m'', res2) <- go m' failure final
                    expr' <- annotateExpression expr
                    return (label, m'',
                        Ift label expr' success_label failure_label : res1 ++ res2)
                P.WhileStatement expr body -> do
                    label <- make_label
                    old_break <- get_break
                    put_break final
                    old_continue <- get_continue
                    put_continue label
                    (body_label, m', res) <- go m body label
                    put_break old_break
                    put_continue old_continue
                    expr' <- annotateExpression expr
                    return (label, m', Ift label expr' body_label final : res)
                P.ForStatement decl cond name expr body -> do
                    rec
                        old_scope <- push_scope
                        (decl_label, m', res1) <- go m decl cond_label
                        cond' <- annotateExpression cond
                        cond_label <- make_label
                        old_break <- get_break
                        put_break final
                        old_continue <- get_continue
                        put_continue incr_label
                        (body_label, m'', res2) <- go m' body incr_label
                        (incr_label, m''', res3) <- go m'' (P.AssignmentStatement name expr) cond_label
                        put_break old_break
                        put_continue old_continue
                        restore_scope old_scope
                    return (decl_label, m''', Ift cond_label cond' body_label final : res1 ++ res2 ++ res3)
                P.SwitchStatement expr stmt -> do
                    -- TODO!!!
                    old_break <- get_break
                    put_break final
                    res <- go m stmt final
                    put_break old_break
                    return res
                P.ReturnStatement expr -> do
                    label <- make_label
                    expr' <- annotateExpression expr
                    return (label, m, [Leave label expr'])
                P.GotoStatement name -> do
                    return (goto name, m, [])
                P.BreakStatement -> do
                    break <- get_break
                    return (break, m, [])
                P.ContinueStatement -> do
                    continue <- get_continue
                    return (continue, m, [])
                P.DeclarationStatement decl Nothing -> do
                    declareVariable decl
                    return (final, m, [])
                P.DeclarationStatement decl (Just expr) -> do
                    declareVariable decl
                    name <- declareVariable decl
                    go m (P.AssignmentStatement name expr) final
                P.CaseStatement num stmt -> do
                    error "TODO: case statement"
                P.DefaultStatement stmt -> do
                    error "TODO: default statement"
                P.LabeledStatement name stmt -> do
                    case M.lookup name (fst m) of
                        Just label ->
                            error $ "attempting to use label `" ++ name ++ "` twice"
                        Nothing -> do
                            (label, (m', o), res) <- go m stmt final
                            return (label, (M.insert name label m', o), res) in

    -- Result
    let leave_node = Leave 0 P.UnitExpression in
    let entry_node = Entry parameters first_label in
    (M.toList label_map, leave_node : entry_node : result)

nodesToEdges :: [Node] -> [(Node, Label, [Label])]
nodesToEdges nodes =
    fmap toEdge nodes
    where
        -- Nodes Jmp apontam apenas para um lugar
        toEdge node@(Jmp label _ next) =
            (node, label, [next])
        -- Nodes Ift apontam para dois lugares
        toEdge node@(Ift label _ success failure) =
            (node, label, [success, failure])
        -- Nodes Leave não vão pra lugar nenhum
        toEdge node@(Leave label _) =
            (node, label, [])
        -- Só temos um nó Entry, que aponta para o começo
        toEdge node@(Entry _ label) =
            (node, 1, [label])
