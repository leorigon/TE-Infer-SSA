module Converter where

import qualified BasicBlock as B
import qualified Parser as P
import qualified Lambda.Calculus as LC
import qualified Data.Map as M
import Debug.Trace

block_prefix = "B"

to_lambda (P.Algorithm name params _) nodes dom_tree =
    result
    where
        result = foldr 
                add_parameter body params
            where
                add_parameter (P.Declarator _ id) node =
                    LC.Lambda (id ++ "0") node

        entry = node_map M.! 1

        node_map = M.fromList [ (B.get_id n, n) | n <- nodes ]
        dom_map = M.fromList dom_tree

        body :: LC.Expr
        body = convert_block entry 
            
        convert_block (B.Entry _ destination) = make_children 1 $ goto 1 destination
        convert_block (B.Jmp source command destination) =
            let jump = make_children source (goto source destination) in
            LC.Lambda "_" $ case command of
                B.CommandAssign var num expr ->
                    let name = var ++ show num in
                    LC.Application (LC.Lambda name jump) (convert_expr expr)
                B.CommandCall func params ->
                    let call = convert_expr (P.CallExpression func params) in
                    LC.Application (LC.Lambda "_" jump) call
        convert_block (B.Ift source expr success failure) =
            let expr' =  convert_expr expr in
            LC.Lambda "_" $
                make_children source $
                    LC.If expr' (goto source success) (goto source failure)
        convert_block (B.Phi var num _ node) =
            let name = var ++ show num in
            LC.Lambda name $ convert_block node
        convert_block (B.Leave _ expr) =
            LC.Lambda "_" $ convert_expr expr

        goto source destination =
            let name = LC.Free $ block_prefix ++ show destination in
            flip LC.Application LC.UnitValue $
                apply_parameters source (node_map M.! destination) name

        apply_parameters source (B.Phi var num actual_parameters destination) lambda =
            let map = M.fromList actual_parameters in
            let this_param = LC.Free $ var ++ show (map M.! source) in
            let application = LC.Application lambda this_param in
            apply_parameters source destination application
        apply_parameters _ _ lambda = lambda
        
        make_children source jump =
            let dominated = dom_map M.! source in
            let children = fmap make_child dominated in
            if (length dominated) > 0 then
                LC.Where children jump
            else jump
            where
                make_child id =
                    (block_prefix ++ show id, convert_block $ node_map M.! id)

        convert_expr (P.VarExpression var) =
            -- This should never happn!!!!
            error "unrecheable"
        convert_expr (P.NumExpression num) =
            LC.Number num
        convert_expr (P.IndexedVarExpression var num) =
            LC.Free (var ++ show num)
        convert_expr (P.StrExpression str) =
            LC.Text str   
        convert_expr (P.EqualsExpression left right) =
            LC.Operation LC.Eq (convert_expr left) (convert_expr right)
        convert_expr (P.AddExpression left right) =
            LC.Operation LC.Sum (convert_expr left) (convert_expr right)
        convert_expr (P.MulExpression left right) =
            LC.Operation LC.Mul (convert_expr left) (convert_expr right)
        convert_expr (P.SubExpression left right) =
            LC.Operation LC.Sub (convert_expr left) (convert_expr right)
        convert_expr (P.DivExpression left right) =
            LC.Operation LC.Div (convert_expr left) (convert_expr right)
        convert_expr (P.LessThanExpression left right) =
            LC.Operation LC.Lt (convert_expr left) (convert_expr right)
        convert_expr (P.MoreThanExpression left right) =
            LC.Operation LC.Gt (convert_expr left) (convert_expr right)
        convert_expr (P.CallExpression func params) =
            let apply_param f expr = LC.Application f (convert_expr expr) in
            let call = foldl apply_param (LC.Free func) params in
            --flip LC.Application LC.UnitValue $
                call
        convert_expr (P.UnitExpression) = LC.UnitValue
        convert_expr (P.BoolExpression b) =
            if b then
                LC.TrueValue
            else
                LC.FalseValue
