{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE TypeFamilies           #-} 
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE StandaloneDeriving     #-}



module AlgGraphs where

import Algebra.Graph.Class
import Algebra.Graph.AdjacencyMap as AdjMap
import Algebra.Graph.NonEmpty.AdjacencyMap (fromNonEmpty)
import Algebra.Graph.AdjacencyMap.Algorithm


import GHC.Exts (Constraint)
import Data.List
import Data.Tree
import Debug.Trace
import Category


-- EF comonad over graph using algebraic adjaceny map graphs. 

-- Invarients:
--    - Graphs should not have more than one of the same vertex

-- class Graph g where
--     type Vertex g
--     empty :: g
--     vertex :: Vertex g -> g
--     overlay :: g -> g -> g
--     connect :: g -> g -> g

data GraphMorphism a b where GM :: (Graph a, Graph b) => (Vertex a -> Vertex b) -> GraphMorphism a b 

instance Category GraphMorphism where
    type Object GraphMorphism g = Graph g
    id          = GM Prelude.id
    GM f . GM g = GM (f Prelude.. g)

-- I think this could probably be better done with coerce
class Graph g => GraphExtras g where
    getEdges :: g -> [(Vertex g, Vertex g)]
    getVertices :: g -> [Vertex g]

-- one of these two defns
-- data EF a where EFdata :: Graph [a] => a -> EFdata a
data EF a where EFdata :: (Graph a, Ord a) => AdjacencyMap [Vertex a] -> EF a

deriving instance (Graph a, Ord a, Show a, Ord (Vertex a), Show (Vertex a)) => Show (EF a)

instance (Graph a, Ord a, Ord (Vertex a)) => Graph (EF a) where
    type Vertex (EF a) = [Vertex a]
    empty = EFdata AdjMap.empty
    vertex v = EFdata $ AdjMap.vertex v
    overlay (EFdata g1) (EFdata g2) = EFdata $ AdjMap.overlay g1 g2
    connect (EFdata g1) (EFdata g2) = EFdata $ AdjMap.connect g1 g2

instance GraphExtras (EF a) where
    getEdges (EFdata g) = edgeList g
    getVertices (EFdata g) = vertexList g


instance CFunctor EF GraphMorphism GraphMorphism where
     funcMap (GM f) = GM (map f)

instance CComonad EF GraphMorphism where
    counit          = GM last -- the universe of EF is none empty lists so this is ok
    extend (GM f)   = GM $ map f Prelude.. (tail Prelude.. inits) 

data Product a b where Prod :: (Graph a, Graph b) => AdjacencyMap (Vertex a, Vertex b) -> Product a b

instance (Graph a, Graph b) => Graph (Product a b) where
    type Vertex (Product a b) = (Vertex a, Vertex b)
    empty = Prod AdjMap.empty
    vertex v = Prod $ AdjMap.vertex v
    overlay (Prod g1) (Prod g2) = Prod $ AdjMap.overlay g1 g2
    connect (Prod g1) (Prod g2) = Prod $ AdjMap.connect g1 g2

instance GraphExtras (Product a b) where
    getEdges (Prod g) = edgeList g
    getVertices (Prod g) = vertexList g

instance CBifunctor Product GraphMorphism GraphMorphism GraphMorphism where
  bifuncMap (GM gm1) (GM gm2) = GM (\(x,y) -> (gm1 x, gm2 y))

-- finish defen
product :: AdjacencyMap a -> AdjacencyMap b -> Product (AdjacencyMap a) (AdjacencyMap b)
product g1 g2 = Prod $ box g1 g2


-- finish coproduct implementation
data Coproduct a b where Coprod :: (Graph a, Graph a) => AdjacencyMap (Either (Vertex a) (Vertex b)) -> Coproduct a b

instance (Graph a, Graph b) => Graph (Coproduct a b) where
    type Vertex (Coproduct a b) = Either (Vertex a) (Vertex b)
    empty = Coprod AdjMap.empty
    vertex v = Coprod $ AdjMap.vertex v
    overlay (Coprod g1) (Coprod g2) = Coprod $ AdjMap.overlay g1 g2
    connect (Coprod g1) (Coprod g2) = Coprod $ AdjMap.connect g1 g2

instance GraphExtras (Coproduct a b) where
    getEdges (Coprod g) = edgeList g
    getVertices (Coprod g) = vertexList g

instance CBifunctor Coproduct GraphMorphism GraphMorphism GraphMorphism where
  bifuncMap (GM gm1) (GM gm2) = GM g
    where g (Left x)  = Left $ gm1 x
          g (Right x) = Right $ gm2 x

coproduct :: AdjacencyMap a -> AdjacencyMap b -> Coproduct (AdjacencyMap a) (AdjacencyMap b)
coproduct g1 g2 = Coprod $ AdjMap.connect (gmap Left g1) (gmap Right g2)

------------------ Example with two equivilent graphs  -------------------- 

-- graph1 :: AdjacencyMap Int
-- graph1 = AdjMap.edges [(1,2),(2,3)]

-- graph2 :: AdjacencyMap Char
-- graph2 = AdjMap.edges [('a','b'),('b','c')]

-- -- universe of a graph
-- universe :: (GraphExtras a, Eq (Vertex a)) => a -> [Vertex a]
-- universe = nub Prelude.. getVertices


-- --given a universe gives all possbile plays for a k length game
-- plays :: Int -> [a] -> [[a]]
-- plays 1 uni = map (\x -> [x]) uni
-- plays k uni = ps ++ [(x:p)|x<-uni,p<-ps]
--     where ps = plays (k-1) uni

-- -- Given a graph map each vertex to every play that is appears in and generate edges accordingly
-- -- Usually gives a massive graph
-- graphToMaxEFk :: (GraphExtras a, Eq (Vertex a)) => Int -> a -> EF a
-- graphToMaxEFk k g = EFdata $ concatMap (\(x,y)->[(f x p1,f y p2)|p1<-ps,p2<-ps,elem x p1,elem y p2]) (getEdges g)
--     where ps       = plays k (universe g)
--           f y (x:xs)
--             | x==y      = x:xs
--             | otherwise = x:(f y xs)

-- -- Given a graph map each vertex to every play that is appears in and generate edges accordingly
-- -- Usually gives a massive graph
-- graphToReasonableEFk :: (GraphExtras a, Eq (Vertex a)) => Int -> a -> EF a
-- graphToReasonableEFk k g = EFdata $ concatMap (\(x,y)->take 5 [(f x p1,f y p2)|p1<-ps,p2<-ps,elem x p1,elem y p2]) (getEdges g)
--     where ps       = plays k (universe g)
--           f y (x:xs)
--             | x==y      = x:xs
--             | otherwise = x:(f y xs)

-- This doesnt really make sense as a thing. The EF comonad should probably map each vertex
-- to all plays ending in that vertex, and the edges acordingly to that. Then when the 
-- EF a -> b morphism was applied we would get to a graph with a load of duplicate edges.
-- If we removed these we should get the graph b. This would probably actually be what we want.

-- It actually does make sense. A coalgebra (which is what this is) needs to map to a prefix closed
-- subset of A^(>=k). I.e. some particular play and its prefixes. This is given by the coalgebra
-- conditions.  If it doesn't preserve all edges its invalid becuase its not a homomorphism
-- Look at page 23 or struct and powerAce23578ac
-- graphToEFk :: (Graph a, Eq (Vertex a)) => [Vertex a] -> a -> EF a
    
-- Given a list of plays for a coalgebra 
-- e.g. for universe [1,2,3,4,5] and k=2 plays might be [[3,2],[1,5],[4]] 
--      the result for x=2 will be [3,2] and for x=1, [1]
-- xToPlay :: Eq a => a -> [[a]] -> [a]
-- xToPlay x plays = reverse (g x (head (filter (elem x) plays)) []) 
--     where g x [] _ = [x]
--           g x (m:ms) ps
--             | m==x      = x:ps
--             | otherwise = g x ms (m:ps)

-- -- Generate all breakings up of the universe into lists of length k plus remainder
-- -- e.g. for universe [1,2,3,4,5,6,7], k=3 generates all possible lists of the form
-- -- [[1,2,3],[4,5,6],[7]] or [[7,4,3],[2,5,6],[1]] and so on. Then maps each node in
-- -- the graph to the prefix of the list it occurs in (xToPlay).
-- genCoalgs :: (GraphExtras a, Eq (Vertex a)) => Int -> a -> [EF a]
-- genCoalgs k g = map (\p -> gmap (\x -> xToPlay x p) g) plays
--     where plays = map (t k) (permutations (universe g))
          
-- t :: Int -> [a] -> [[a]]
-- t k xs
--   | k < (length xs) = (take k xs) : (t k (drop k xs))
--   | otherwise       = [xs]





-- liftMappingToEFMorphism ::(Graph a, Graph b) => (Vertex a -> Vertex b) -> GraphMorphism (EF a) b
-- liftMappingToEFMorphism f = GM f Category.. counit

-- myhomomorph :: GraphMorphism (EF (MyGraph Int)) (MyGraph Char) 
-- myhomomorph = liftMappingToEFMorphism f 
--   where f 1 = 'a'
--         f 2 = 'b'
--         f 3 = 'c'

-- apply :: (Graph a, Graph b, Eq (Vertex b)) => GraphMorphism a b -> a -> b
-- apply (GM gm) = gmap gm

--res1 = apply myhomomorph (head (liftGraphToEFkGraphs 1 graph1)) == graph2

-- ------------------ Example with linear orderings  -------------------- 
-- -- Given a list representing a linear ordering it returns the equivilent
-- -- graph with the edge relation interpreted as the < relation
-- linToGraph :: [a] -> MyGraph a
-- linToGraph xs = MyGraph (f xs)
--   where f [] = []
--         f (x:xs) = map (\y -> (x,y)) xs ++ f xs

-- count :: Eq a => a -> [a] -> Int
-- count x = foldr (\y xs-> if x==y then xs + 1 else xs) 0

-- -- converts a graph to a linear order
-- -- Pre: Graph is a representation of a lin order
-- graphToLin :: (Graph a, Eq (Vertex a)) => a -> [Vertex a]
-- graphToLin g = reverse $ map fst $ sortBy (\(_,a) (_,b) -> compare a b) $ map (\x -> (x,count x e)) (universe g)
--     where e = map fst (edges g)

-- -- Pre: elem x xs
-- split :: Eq a => a -> [a] -> ([a],[a])
-- split x xs = f [] xs
--     where f xs (y:ys) = if x == y then (reverse (x:xs), x:ys) else f (y:xs) ys
          
-- -- Get pos of y in xs
-- -- Pre: y is in xs
-- index y xs = f xs 0
--     where f (x:xs) i
--             | x == y    = i
--             | otherwise = f xs (i+1)

-- -- Pre: x is in the iso
-- getIso :: Eq a => [(a,b)] -> a -> b
-- getIso ((a,b):iso) x 
--     | x == a     = b
--     | otherwise  = getIso iso x

-- -- Given a spoilers play come up with the duplicators 
-- -- This uses the strategy given on page 29 of Libkin
-- -- Pre: length lin1,lin2 >= 2^k
-- --      length spoil <= k
-- strategy :: (Graph a, Graph b, Eq (Vertex a), Eq (Vertex b)) => Int -> a -> b -> [Vertex a] -> [Vertex b]
-- strategy k glin1 glin2 spoil = map (getIso iso) spoil
--     where lin1 = graphToLin glin1
--           lin2 = graphToLin glin2
--           iso  = f k lin1 lin2 spoil

-- inIso :: Eq a => a -> [(a,b)] -> Bool
-- inIso x []    = False
-- inIso x ((a,b):ps)
--     | x==a      = True 
--     | otherwise = inIso x ps

-- f :: Eq a => Int -> [a] -> [b] -> [a] -> [(a,b)]
-- f _ _ _ [] = []
-- f 0 _ _ _  = []
-- f k lin1 lin2 (p:ps)
--     | inIso p iso = iso
--     | otherwise   = (p,chooseb k lin1 lin2 p) : iso
--       where iso   = f (k-1) lin1 lin2 ps


-- -- This is the function that given an 'a' in lin1 finds a 'b' in lin2 s.t. lin1 - a =_(k-1) lin2 - b
-- chooseb :: Eq a => Int -> [a] -> [b] -> a -> b
-- chooseb k lin1 lin2 a
--     | length lin1LT < 2^(k-1) = lin2 !! index a lin1
--     | length lin1GT < 2^(k-1) = lin2 !! index a lin1
--     | otherwise               = lin2 !! (2^(k-1))
--     where (lin1LT,lin1GT) = split a lin1



-- buildMorphEFkAtoB :: (Graph a, Graph b, Eq (Vertex a), Eq (Vertex b)) => Int -> a -> b -> GraphMorphism (EF a) b
-- buildMorphEFkAtoB k glin1 glin2 = GM (last Prelude.. strategy k glin1 glin2)

-- checkEFkMorph :: (Graph a, Graph b, Eq (Vertex b), Eq (Vertex a)) => Int -> a -> b -> b
-- checkEFkMorph k glin1 glin2 = apply (buildMorphEFkAtoB k glin1 glin2) eflin1
--     where eflin1 = head $ genCoalgs k glin1

-- lin1 = linToGraph [1..17]
-- lin2 = linToGraph [3..22]

-- lin3 = linToGraph [1,2,3]

-- lin4 = linToGraph [1..9]
-- lin5 = linToGraph [4..12]

-- lin6 = linToGraph [1..4]
-- lin7 = linToGraph [5..8]

------------------ Tree depth experiments  -------------------- 

data Gaifman a where Gaifman :: (Graph a, Ord a, Ord (Vertex a)) => AdjacencyMap (Vertex a) -> Gaifman a

-- The gaifman graph is undirected and irreflexive (no self edges)
getGaifmanGraph :: Ord a => AdjacencyMap a -> Gaifman (AdjacencyMap a)
getGaifmanGraph g = Gaifman $ AdjMap.edges (nub (concat [[(v1,v2),(v2,v1)] |(v1,v2) <- (edgeList g), v1 /= v2]))

-- Get connected componants of a Gaifman graph
getCC :: Gaifman (AdjacencyMap a) -> [Gaifman (AdjacencyMap a)]
getCC (Gaifman g) = map (Gaifman Prelude.. fromNonEmpty) $ vertexList $ scc g

-- Tree depth decomposition of the Gaifman graph

-- A treedepth decomposition of a connected graph G=(V,E) is a rooted tree T=(V,ET) that
-- can be obtained in the following recursive procedure. If G has one vertex, then T=G.
-- Otherwise pick a vertex v∈V as the root of T, build a treedepth decomposition of each
-- connected component of G−v and add each of these decompositions to T by making its root
-- adjacent to v
gaifmanTDD :: Gaifman (AdjacencyMap a) -> Tree a
gaifmanTDD (Gaifman g)
    | vertexCount g == 1 = Node {rootLabel = (head (vertexList g)), subForest = []}
    | otherwise          = Node {rootLabel = v,subForest = map gaifmanTDD cc}
        where v  = head (vertexList g)
              cc = getCC (Gaifman (removeVertex v g))

