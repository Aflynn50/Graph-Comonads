module DrawGraphs where

import Algebra.Graph.AdjacencyMap as AdjMap
import Data.Tree

import Data.GraphViz
    ( graphElemsToDot,
      nonClusteredParams,
      runGraphviz,
      GraphvizOutput(DotOutput),
      DotGraph,
      PrintDot )

graphVizParams = nonClusteredParams

-- graphToDot :: (Ord a, Show a) => AdjacencyMap a -> DotGraph a
-- graphToDot g = graphElemsToDot graphVizParams (map (\x -> (x,show x)) vs) (map (\(x,y)->(x,y,"")) es)
--     where vs = vertexList g
--           es = edgeList g

graphToDot :: (Ord a, Show a) => AdjacencyMap a -> DotGraph String
graphToDot g = graphElemsToDot graphVizParams (map (\x -> (show x,show x)) vs) (map (\(x,y)->(show x,show y,"")) es)
    where vs = vertexList g
          es = edgeList g

-- Use the graphviz visual studio extention with the preview to see graph
-- Open graph.dot, Ctrl+p, type '>' and select Graphviz interactive preview
printGraph :: (Ord a, Show a) => AdjacencyMap a -> IO String
printGraph g = runGraphviz (graphToDot g) DotOutput "./graph.dot"

printGraphs :: (Ord a, Show a) => [AdjacencyMap a] -> IO String
printGraphs gs = printGraph $ foldr (\x g -> overlay x g) empty (map indexGraph (zip [1..] gs))

indexGraph :: (Show a, Ord a) => (Int,AdjacencyMap a) -> AdjacencyMap String
indexGraph (n,g) = gmap (\x -> show (n,x)) g

treeMap :: (a -> b) -> Tree a -> Tree b
treeMap f (Node x xs) = (Node (f x) (map (treeMap f) xs))

printTree :: Show a => Tree a -> IO ()
printTree t = printForest [t]

printForest :: Show a => [Tree a] -> IO ()
printForest f = putStr $ drawForest $ map (treeMap show) f