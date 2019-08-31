import System.IO

import qualified Lexer as L
import qualified Parser as P
import qualified BasicBlock as B
import qualified Data.Graph as G
import qualified Dominance as D
import qualified Effect as E
import qualified SingleAssignment as S
import qualified Converter as C
import qualified Lambda.Calculus as LC
import qualified Lambda.Lexer as LL
import qualified Lambda.Parser as LP
import qualified Lambda.Inference as LI
import Data.Char
import Data.List
import Control.Monad

showTokens [] = return ()

showTokens ((line, column, text, token):xs) = do
    putStrLn $ "  " ++ show line ++ ":" ++ show column ++ " = " ++ show token ++ " `" ++ text ++ "`"
    showTokens xs

showNodesDot _ [] = do { return (); } 

showNodeDot handle (B.Phi var num values node) prefix = do
      showNodeDot handle node (var ++ subscript num ++ " = φ(" ++ intercalate ", " values' ++ ")\\n" ++ prefix)
      where
        subscript = map (chr . (+) 0x2050 . ord) . show
        values' = map local_value values
        local_value (label, num) = var ++ subscript num

showNodeDot handle (B.Entry params label) _ = do
      hPutStrLn handle $ "  b1 [label=\"b1: Entry: " ++ show params ++ "\"];"
      hPutStrLn handle $ "  b1 -> b" ++ show label ++ ";"

showNodeDot handle (B.Leave from expr) prefix = do
      hPutStrLn handle $ "  b" ++ show from ++ " [label=\"b" ++ show from ++ ": " ++ prefix ++ "RETURN " ++ show expr ++ "\"];"

showNodeDot handle (B.Jmp from cmd to) prefix = do
      hPutStrLn handle $ "  b" ++ show from ++ " [shape=box, label=\"b" ++ show from
                           ++ ":\\n" ++ prefix ++ show cmd ++ "\"];"
      hPutStrLn handle $ "  b" ++ show from ++ " -> b" ++ show to ++ ";"

showNodeDot handle (B.Ift from expr success failure) prefix = do
      hPutStrLn handle $ "  b" ++ show from ++ " [shape=box, label=\"b" ++ show from ++ ":\\n" ++ prefix ++ show expr ++ "?\"];"
      hPutStrLn handle $ "  b" ++ show from ++ " -> b" ++ show success ++ " [label=true];"
      hPutStrLn handle $ "  b" ++ show from ++ " -> b" ++ show failure ++ " [label=false];"

showNode (B.Entry params label) = do
      putStrLn $ "  1: Entry: " ++ show params ++ "; goto " ++ show label

showNode (B.Jmp from cmd to) = do
      putStrLn $ "  " ++ show from ++ ": " ++ show cmd ++ "; goto " ++ show to

showNode (B.Ift from expr success failure) = do
      putStrLn $ "  " ++ show from ++ ": goto " ++ show expr ++ " ? " ++ show success ++ " : " ++ show failure

showNode (B.Leave from expr) = do
      putStrLn $ "  " ++ show from ++ ": return " ++ show expr

writeDotFile nodes dominators = do
  handle <- openFile "out.dot" WriteMode
  hPutStrLn handle "digraph g {"
  mapM (\(x, y) -> do
      hPutStrLn handle $ "  d" ++ show x ++ " [label=b" ++ show x ++ "];"
      when (x /= y) $ do
        hPutStrLn handle $ "  d" ++ show y ++ " -> d" ++ show x ++ ";"
      showNodeDot handle (nodes !! x) ""
    ) dominators
  hPutStrLn handle "}"
  hClose handle

showToplevel (env, effs) (P.Handler name cases) = do
      putStrLn $ "\nAdding handler " ++ name ++ "..."
      let which@(effect, _) = E.decideEffectHandler cases effs
    
      bodies <- flip mapM cases $ \c -> do
    
        let (name, params, body) = case c of
                                       -- If we don't have a parameter, pretend we have
                                       -- one (that will be unit)
                                       P.HandlerCase name [] b -> (Just name, ["_"], b)
                                       P.HandlerCase name xs b -> (Just name, xs, b)
                                       P.HandlerPure x b -> (Nothing, [x], b)
        let algorithm = P.Algorithm "" (fmap (P.Declarator P.TypeVar) params) body
        converted <- astToLambda algorithm
        return (name, converted)
    
      let handler = LC.Handler effect bodies
    
      putStrLn "\nInfered type:"
      let it = LI.runInferer handler env
      print it
    
      return (LC.extend env name it, effs)
    
showToplevel (env, effs) (P.Effect name funs) = do
      let (decls, eff) = E.effectIntoDeclarations name funs env
      return (foldl (\e (n, t) -> LC.extend e n t) env decls, eff : effs)

showToplevel (env, effs) algorithm@(P.Algorithm f p s) = do
      --putStrLn $ "\nChecking function " ++ f ++ "..."
      converted <- astToLambda algorithm
      --
      --putStrLn "\nContext before inference:"
      --print env
      --
      putStrLn "\nInfered type:"
      let it = LI.runInferer converted env
      print it
      --
      return (LC.extend env f it, effs)

astToLambda algorithm@(P.Algorithm f p s) = do
      --putStrLn "\nNodes:"
      let (label_map, nodes) = B.astToNodes s p
      --mapM showNode nodes
      let edges = B.nodesToEdges nodes
      --putStrLn "\nEdges:"
      --print edges
      let (graph, _, _) = G.graphFromEdges edges
      --putStrLn "\nGraph:"
      --putStrLn $ "  " ++ show graph
      let (dominators, i_dominators, dom_tree, frontier) = D.dominators graph
      -- putStrLn "\nDominators:"
      -- putStrLn $ "  " ++ show dominators
      -- putStrLn "\nImmediate Dominators:"
      -- putStrLn $ "  " ++ show i_dominators
      -- putStrLn "\nDominator tree:"
      -- putStrLn $ "  " ++ show dom_tree
      -- putStrLn "\nDominance Frontier:"
      -- putStrLn $ "  " ++ show frontier
      -- putStrLn "\nKnown variables:"
      let known_variables = S.findKnownVariables nodes
      --putStrLn $ "  " ++ show known_variables
      let phi_nodes = S.enumaratePhiNodes nodes dominators i_dominators frontier
      --putStrLn "\nPhi Nodes Needed:"
      --putStrLn $ "  " ++ show phi_nodes
      --putStrLn "\nRenamed:"
      let renamed = S.rename graph nodes known_variables dom_tree phi_nodes
      --putStrLn $ "  " ++ show renamed
      writeDotFile renamed i_dominators
      putStrLn "\nConverted:"
      let converted = C.to_lambda algorithm renamed dom_tree
      putStrLn $ show converted
      return converted

main = do
      -- putStrLn "Lexer:"
      input <- readFile "test.lc"
      let l = L.lex input
      -- print l
      -- putStrLn "\nParser:"
      let p = P.parse l
      -- print p
      (env, _) <- foldM showToplevel (LI.initialEnvironment, []) p

      putStrLn "\nFinal environment:"
      print env

{- 
      -- For debug/infer directly lambda calculus   
    
      input <- readFile "test.txt"
      putStrLn "Lexer:"
      let l = LL.lex input
      print l
      putStrLn "\nParser:"
      let p = LP.parse l
      print p
      putStrLn "\nInfered type:"
      let it = LI.runInferer p
      print it
  
-}
