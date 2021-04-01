module DrawGraphs where

import Algebra.Graph.AdjacencyMap as AdjMap

import Data.GraphViz

graphVizParams = nonClusteredParams

mygraphToDot :: (Ord a, Show a) => AdjacencyMap a -> DotGraph a
mygraphToDot g = graphElemsToDot graphVizParams (map (\x -> (x,show x)) vs) (map (\(x,y)->(x,y,"")) es)
    where vs = vertexList g
          es = edgeList g

-- Use the graphviz visual studio extention with the preview to see graph
-- Open graph.dot, Ctrl+p, type '>' and select Graphviz interactive preview
printGraph g = runGraphviz (mygraphToDot g) DotOutput "./graph.dot"