{-# LANGUAGE FlexibleContexts #-}
module SingleAssignment where

import qualified Parser as P
import qualified BasicBlock as B
import qualified Data.Set as S
import qualified Data.Map.Lazy as M
import Control.Monad.State.Lazy
import Debug.Trace

enumaratePhiNodes nodes dominators i_dominators frontiers =
    let assigns = findAssignments nodes in
    let known_variables = findKnownVariables nodes in
    let phi_nodes = map (blocksWithPhiFor assigns frontiers) known_variables in
    zip known_variables phi_nodes

blocksWithPhiFor assigns frontiers var =
    -- List of blocks that assign `var`
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
