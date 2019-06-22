module Dominance where

  import Data.Array
  import Data.Graph
  import Data.List hiding ( intersect )
  import Data.Map ( Map )
  import qualified Data.Map as Map
  import Data.Set (Set)
  import qualified Data.Set as Set
  
  dominators g =
      let dom_tree = Map.toList (genDomTree g) in
      let i_dominators = [ vertex |
                           vertex <- dom_tree, path g 1 (fst vertex) ] in
      let dominators = Map.fromList $ [ (x, nub . sort $ y :
                                              if y == 1 then [] else dominators Map.! y)
                                          | (x, y) <- i_dominators, x /= 1 ] in
      let (0, len) = bounds g in
      let a `d` b = a == b || case dominators Map.!? b of
                                  Nothing -> False
                                  Just list -> elem a list in
      let a `sd` b = (a `d` b) && a /= b in
      let pred n = nub [ a | (a, b) <- edges g, n == b ] in
      let dominance_frontier n =
              [ y | y <- [0..len],
                  any (\z -> n `d` z) (pred y) && not (n `sd` y) ] in
      let frontier = [ (n, dominance_frontier n) | n <- [0..len] ] in
      let dom_tree = [ (n, sort [ x |
                                  (x, d) <- i_dominators, d == n, x /= 1 ]) |
                        n <- [0..len] ] in
      (Map.toList dominators, i_dominators, dom_tree, frontier)
  
  -- http://hackage.haskell.org/package/cao-0.1/src/src/Language/CAO/Analysis/Dominance.hs
  
  --------------------------------------------------------------------------------
  {- DOMINATOR TREE -}
  -- pag 13
  
  -- for all nodes, b /* initialize the dominators array */
  -- doms[b] <- Undefined
  -- doms[start node] <- start node
  -- Changed <- true
  -- while (Changed)
  --    Changed <- false
  --    for all nodes, b, in reverse postorder (except start node)
  --      new idom <- first (processed) predecessor of b /* (pick one) */
  --      for all other predecessors, p, of b
  --        if doms[p] /= Undefined /* i.e., if doms[p] already calculated */
  --          new idom <- intersect(p, new idom)
  --      if doms[b] /= new idom
  --        doms[b] <- new idom
  --        Changed <- true
  --
  
  genDomTree :: Graph -> Map Vertex Vertex
  genDomTree g = let
          (ns, ss) = partition withPreds (vertices g)
          initSelf = foldl' (\m n -> Map.insert n n m) Map.empty ss
      in genDomTree' ns initSelf
      where
      genDomTree' :: [Vertex] -> Map Vertex Vertex -> Map Vertex Vertex
      genDomTree' ns doms = let doms' = foldl' (upDomTree g) doms ns
          in if doms' == doms then doms else genDomTree' ns doms'
  
      withPreds :: Vertex -> Bool
      withPreds = not . null . predecessors g
  
  upDomTree :: Graph -> Map Vertex Vertex -> Vertex -> Map Vertex Vertex
  upDomTree g doms b = Map.alter alterNewIdiom b doms
      where
      alterNewIdiom :: Maybe Vertex -> Maybe Vertex
      alterNewIdiom = const $ Just $ getNewIdiom $ predecessors g b
  
      getNewIdiom :: [Vertex] -> Vertex
      getNewIdiom (p:ps) = foldl' fNewIdiom p ps
      getNewIdiom _      = error $ "<Language.CAO.Analysis.Dominance>.\
          \<updDomTree>: no predecessors!"
  
      fNewIdiom :: Vertex -> Vertex -> Vertex
      fNewIdiom ni p = if Map.member p doms then intersect p ni doms else ni
  
  predecessors :: Graph -> Vertex -> [Vertex]
  predecessors g v = [ a | (a, b) <- edges g, b == v]
  
  successors :: Graph -> Vertex -> [Vertex]
  successors   g v = [ b | (a, b) <- edges g, a == v]

  intersect :: Vertex -> Vertex -> Map Vertex Vertex -> Vertex
  intersect v1 v2 doms
      = maximum [ f1 | f1 <- follow v1 , f1 `elem` follow v2 ]
      where
      follow :: Vertex -> [Vertex]
      follow v = case Map.lookup v doms of
          Just v' | v > v' -> v : follow v'
          _                -> [v]
  
  domFront :: Graph -> Map Vertex (Set Vertex)
  domFront g = foldl' (nodeDomFront g doms) Map.empty $ vertices g
      where
      doms :: Map Vertex Vertex
      doms = genDomTree g
  
  
  nodeDomFront :: Graph
               -> Map Vertex Vertex
               -> Map Vertex (Set Vertex)
               -> Vertex
               -> Map Vertex (Set Vertex)
  nodeDomFront g doms df b = let
          preds = predecessors g b
      in case preds of
          _:_:_ -> foldl' addDoms df preds
          _     -> df
      where
      addDoms :: Map Vertex (Set Vertex)
              -> Vertex
              -> Map Vertex (Set Vertex)
      addDoms df' = foldl' addDom df' . follow
  
      addDom :: Map Vertex (Set Vertex)
             -> Vertex
             -> Map Vertex (Set Vertex)
      addDom = flip (Map.alter dfSet)
  
      dfSet :: Maybe (Set Vertex) -> Maybe (Set Vertex)
      dfSet Nothing  = Just $ Set.singleton b
      dfSet (Just s) = Just $ Set.insert b s
  
      follow :: Vertex -> [Vertex]
      follow r = case Map.lookup r doms of
          Just d | d /= r -> r : follow d
          _               -> [r]
  
  invertMap :: Map Vertex Vertex -> Map Vertex [Vertex]
  invertMap domTree = Map.foldrWithKey aux (Map.map (const []) domTree) domTree
      where
      aux :: Vertex -> Vertex -> Map Vertex [Vertex] -> Map Vertex [Vertex]
      aux k v m = if k == v
          then m
          else let newVal = k : Map.findWithDefault [] v m
               in Map.insert v newVal m
