{-# LANGUAGE FlexibleContexts #-}
module SingleAssignment where

import Data.Maybe
import Control.Monad.RWS.Lazy
import Control.Monad.State.Lazy
import Debug.Trace
import qualified Parser as P
import qualified BasicBlock as B
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Array as A

enumaratePhiNodes nodes dominators i_dominators frontiers =
    let assigns = findAssignments nodes in
    let known_variables = findKnownVariables nodes in
    let phi_nodes = map (blocksWithPhiFor assigns frontiers) known_variables in
    zip known_variables phi_nodes

blocksWithPhiFor assigns frontiers var =
    let assigns_var = S.fromList $ map fst $ filter (elem var . snd) assigns in
    S.toList $ evalState go (assigns_var, assigns_var, S.empty)
    where
        whileM_ cond action = do
            res <- cond
            if res
                then action >> whileM_ cond action
                else return ()
        forEachM_ =
            flip mapM_
        getWorkList = do
            (workList, _, _) <- get
            return workList
        getEverOnWorkList = do
            (_, everOnWorkList, _) <- get
            return everOnWorkList
        getAlreadyHasPhi = do
            (_, _, alreadyHasPhi) <- get
            return alreadyHasPhi
        insertPhiNode d = do
            (workList, everOnWorkList, alreadyHasPhi) <- get
            put (workList, everOnWorkList, S.insert d alreadyHasPhi)
        insertIntoWorkList d = do
            (workList, everOnWorkList, alreadyHasPhi) <- get
            put (S.insert d workList, everOnWorkList, alreadyHasPhi)
        insertIntoEverOnWorkList d = do
            (workList, everOnWorkList, alreadyHasPhi) <- get
            put (workList, S.insert d everOnWorkList, alreadyHasPhi)
        takeFromWorkList = do
            (workList, everOnWorkList, alreadyHasPhi) <- get
            let n = S.findMin workList
            put (S.deleteMin workList, everOnWorkList, alreadyHasPhi)
            return n
        notNullM =
            return . not . S.null
        go :: State (S.Set Int, S.Set Int, S.Set Int) (S.Set Int)
        go = do
            whileM_ (getWorkList >>= notNullM) $ do
                n <- takeFromWorkList
                let current_frontier = snd $ frontiers !! n
                forEachM_ current_frontier $ \d -> do
                    alreadyHasPhi <- getAlreadyHasPhi
                    when (not $ S.member d alreadyHasPhi) $ do
                        insertPhiNode d
                        everOnWorkList <- getEverOnWorkList
                        when (not $ S.member d everOnWorkList) $ do
                            insertIntoWorkList d
                            insertIntoEverOnWorkList d
                return ()
            getAlreadyHasPhi

findAssignments =
    map findAssignment
    where
        findAssignment :: B.Node -> (B.Label, [(String, Int)])
        findAssignment (B.Entry params _) =
            (1, map (flip (,) 0 . P.getDeclaratorName) params)
        findAssignment (B.Leave label _) =
            (label, [])
        findAssignment (B.Jmp label (B.CommandAssign s i _) _) =
            (label, [(s, i)])
        findAssignment (B.Jmp label _ _) =
            (label, [])
        findAssignment (B.Ift label _ _ _) =
            (label, [])

findKnownVariables =
    S.toList . foldl S.union S.empty . map (S.fromList . snd) . findAssignments

data Information = ScopeNumbering Int (M.Map (P.Identifier, Int) Int)
                 | InsertPhiNode B.Label (P.Identifier, Int) Int

rename graph nodes known_variables dom_tree phi_nodes =
    result
    where
        entry = node_map M.! 1

        node_map = M.fromList [ (B.get_id node, node) | node <- nodes ]

        idom_map = M.fromList dom_tree

        initial_vars = M.fromList [ (var, 0) | var <- known_variables ]

        info = snd $ execRWS (rename_walker 1 entry) () initial_vars

        --
        name_map :: M.Map Int (M.Map (String, Int) Int)
        name_map = M.fromList (mapMaybe extract_scoping info)
            where
                extract_scoping (ScopeNumbering id vars) = Just (id, vars)
                extract_scoping _ = Nothing

        phi_vars :: M.Map Int (M.Map (String, Int) Int)
        phi_vars = M.fromListWith M.union (mapMaybe extract_phi info)
            where
                extract_phi (InsertPhiNode id var num) = Just (id, M.singleton var num)
                extract_phi _ = Nothing

        result = fmap apply_changes nodes

        apply_changes node =
            let id = B.get_id node in
            case find_dominator id of
                Just dom_id ->
                    let my_phi_vars = M.findWithDefault M.empty id phi_vars in
                    let dom_vars = M.union my_phi_vars (name_map M.! dom_id) in
                    let rename_expr = flip P.setVariablesIndexes (M.mapKeys fst dom_vars) in
                    prependPhiNodes id $ case node of
                        B.Entry _ _ ->
                            node
                        B.Jmp _ (B.CommandAssign var scope expr) target ->
                            let own_vars = name_map M.! id in
                            let local_name = own_vars M.! (var, scope) in
                            B.Jmp id (B.CommandAssign var local_name (rename_expr expr)) target
                        B.Jmp _ (B.CommandCall fun args) target ->
                            B.Jmp id (B.CommandCall fun (fmap rename_expr args)) target
                        B.Ift _ expr success failure ->
                            B.Ift id (rename_expr expr) success failure
                        B.Leave _ expr ->
                            B.Leave id (rename_expr expr)
                Nothing -> node

        prependPhiNodes :: Int -> B.Node -> B.Node
        prependPhiNodes id =
            M.foldrWithKey appendPhiNode Prelude.id (M.findWithDefault M.empty id phi_vars)
            where
                appendPhiNode :: (String, Int) -> Int -> (B.Node -> B.Node) -> B.Node -> B.Node
                appendPhiNode var@(name, _) num f node =
                    let edges = M.toList (value_map var M.! id) in
                    f (B.Phi name num edges node)
        value_map var =
            M.fromList [ (i, find_values i) | n <- nodes, let i = B.get_id n ]
            where
                find_values i =
                    let preds = [ e | (e, x) <- A.assocs graph,
                                       i `elem` x ] in
                    M.fromList [(e, get_num i e) | e <- preds ]
                get_num i e =
                    name_map M.! e M.! var
        find_dominator id =
            fmap fst . M.lookupMin . M.filter (elem id) $ idom_map

        rename_walker dominator node = do
            rename_node dominator node
            let id = B.get_id node
            let children = [ node_map M.! child_id |
                             child_id <- M.findWithDefault [] id idom_map ]
            mapM_ (rename_walker id) children

        rename_node dominator (B.Entry _ _) = do
            tell [ScopeNumbering 1 initial_vars]

        rename_node dominator (B.Jmp id (B.CommandAssign var scope _) _) = do
            vars <- name_phi_vars dominator id
            new_name <- fresh (var, scope)
            let new_vars = M.insert (var, scope) new_name vars
            tell [ScopeNumbering id new_vars]

        rename_node dominator node = do
            let id = B.get_id node
            vars <- name_phi_vars dominator id
            tell [ScopeNumbering id vars]

        name_phi_vars dominator id = do
            let map = name_map M.! dominator
            foldM iterator map phi_nodes
            where
                iterator map (var, nodes) =
                    if elem id nodes then do
                        new_name <- fresh var
                        let new_map = M.insert var new_name map
                        tell [InsertPhiNode id var new_name]
                        return new_map
                    else
                        return map

        fresh var = do
            state <- get
            let new_name = (state M.! var) + 1
            put $ M.insert var new_name state
            return new_name
