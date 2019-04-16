import System.IO
{-
import qualified Lexer as L
import qualified Parser as P
import qualified BasicBlock as B
import qualified Data.Graph as G
import qualified Dominance as D
import qualified SingleAssignment as S

import Control.Monad.State.Lazy

showTokens [] =
  return ()

showTokens ((line, column, text, token):xs) = do
  putStrLn $ "  " ++ show line ++ ":" ++ show column ++ " = " ++ show token ++
    " `" ++ text ++ "`"
  showTokens xs

showNodesDot _ [] = do
  return ()

showNodeDot handle (B.Entry params label) = do
  hPutStrLn handle $ "  b1 [label=\"b1: ENTRADA " ++ show params ++ "\"];"
  hPutStrLn handle $ "  b1 -> b" ++ show label ++ ";"

showNodeDot handle (B.Leave from expr) = do
  hPutStrLn handle $ "  b" ++ show from ++ " [label=\"b" ++ show from ++ ": RETURN " ++ show expr ++ "\"];"

showNodeDot handle (B.Jmp from cmd to) = do
  hPutStrLn handle $ "  b" ++ show from ++ " [shape=box, label=\"b" ++ show from
                           ++ ":\\n" ++ show cmd ++ "\"];"
  hPutStrLn handle $ "  b" ++ show from ++ " -> b" ++ show to ++ ";"

showNodeDot handle (B.Ift from expr success failure) = do
  hPutStrLn handle $ "  b" ++ show from ++ " [shape=box, label=\"b" ++ show from ++ ": " ++ show expr ++ "?\"];"
  hPutStrLn handle $ "  b" ++ show from ++ " -> b" ++ show success ++ " [label=true];"
  hPutStrLn handle $ "  b" ++ show from ++ " -> b" ++ show failure ++ " [label=false];"

showNode (B.Entry params label) = do
  putStrLn $ "  1: ENTRY; " ++ show params ++ "; goto " ++ show label

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
      when (x /= y) $ hPutStrLn handle $ "  d" ++ show y ++ " -> d" ++ show x ++ ";"
      showNodeDot handle (nodes !! x)
    ) dominators
  hPutStrLn handle "}"
  hClose handle

showToplevel (P.Algorithm f p s) = do
  putStrLn "\nNodes:"
  let (label_map, nodes) = B.astToNodes s p
  mapM showNode nodes
  let edges = B.nodesToEdges nodes
  putStrLn "\nEdges:"
  print edges
  let (graph, _, checker) = G.graphFromEdges edges
  putStrLn "\nGraph:"
  putStrLn $ "  " ++ show graph
  let (dominators, i_dominators, dom_tree, frontier) = D.dominators graph
  putStrLn "\nDominators:"
  putStrLn $ "  " ++ show dominators
  putStrLn "\nImmediate Dominators:"
  putStrLn $ "  " ++ show i_dominators
  putStrLn "\nDominance Frontier:"
  putStrLn $ "  " ++ show frontier
  writeDotFile nodes i_dominators
  --
  putStrLn "\nKnown variables:"
  let known_variables = S.findKnownVariables nodes
  putStrLn $ "  " ++ show known_variables
  let phi_nodes = S.enumaratePhiNodes nodes dominators i_dominators frontier
  putStrLn "\nPhi Nodes Needed:"
  putStrLn $ "  " ++ show phi_nodes
  --
  putStrLn "\nDom tree:"
  putStrLn $ "  " ++ show dom_tree
-}

import qualified Lambda.Calculus as LC
import qualified Lambda.Lexer as LL
import qualified Lambda.Parser as LP
import qualified Lambda.Inference as LI

main = do
  {---
  putStrLn "Lexer:"
  input <- readFile "test.pfc"
  let l = L.lex input
  print l
  --
  putStrLn "\nParser:"
  let p = P.parse l
  print p
  --
  mapM showToplevel p
  -}
  input <- readFile "test.txt"
  putStrLn "Lexer:"
  let l = LL.lex input
  print l
  --
  putStrLn "\nParser:"
  let p = LP.parse l
  print p
  --
  putStrLn "\nInfered type:"
  let it = LI.runInferer p
  print it
