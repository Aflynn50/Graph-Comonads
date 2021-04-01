{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE TypeFamilies           #-} 
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE StandaloneDeriving     #-}



module AlgGraphsExamples where

import Algebra.Graph.Class
import Algebra.Graph.AdjacencyMap as AdjMap
import qualified Algebra.Graph.NonEmpty.AdjacencyMap as NonEmptyAdjMap (fromNonEmpty, overlay, edge, edgeList)
import Algebra.Graph.AdjacencyMap.Algorithm


import GHC.Exts (Constraint)
import Data.List
import Data.Maybe
import Data.Coerce
import Data.Tree
import Debug.Trace
import Category
import DrawGraphs
import AlgGraphsCat

------------------ Example with two equivilent graphs  -------------------- 
-- With EF comonad I can only prove them equivilent in fragment of logic with quantifier rank k.
-- To do this we give a coklislie morphism that takes the EK graph with play length k to graph b
graph1 :: AdjacencyMap Int
graph1 = AdjMap.edges [(1,2),(2,3)]

graph2 :: AdjacencyMap Char
graph2 = AdjMap.edges [('a','b'),('b','c')]

g1tog2 = liftMapToEFMorph f 
  where f 1 = 'a'
        f 2 = 'b'
        f 3 = 'c'

g2tog1 = liftMapToEFMorph f 
  where f 'a' = 1
        f 'b' = 2
        f 'c' = 3 





res1 = eqUpToQuantRankK 4 g1tog2 g2tog1 graph1 graph2

------------------ Example with linear orderings  --------------------
-- Given a list representing a linear ordering it returns the equivilent
-- graph with the edge relation interpreted as the < relation
linToGraph :: Ord a => [a] -> AdjacencyMap a
linToGraph xs = AdjMap.edges (f xs)
  where f [] = []
        f (x:xs) = map (\y -> (x,y)) xs ++ f xs

count :: Eq a => a -> [a] -> Int
count x = foldr (\y xs-> if x==y then xs + 1 else xs) 0

-- converts a graph to a linear order
-- Pre: Graph is a representation of a lin order
graphToLin :: (Graph a, GraphExtras a, Eq (Vertex a)) => a -> [Vertex a]
graphToLin g = reverse $ map fst $ sortBy (\(_,a) (_,b) -> compare a b) $ map (\x -> (x,count x e)) (universe g)
    where e = map fst (getEdges g)

-- Pre: elem x xs
split :: Eq a => a -> [a] -> ([a],[a])
split x xs = f [] xs
    where f xs (y:ys) = if x == y then (reverse (x:xs), x:ys) else f (y:xs) ys
          
splitAtD :: Int -> [a] -> ([a],[a])
splitAtD i xs = (\(x,y) -> (x++[head y],y)) $ splitAt i xs

-- Get pos of y in xs
-- Pre: y is in xs
index y xs = f xs 0
    where f (x:xs) i
            | x == y    = i
            | otherwise = f xs (i+1)

-- Pre: x is in the iso
getIso :: Eq a => [(a,b)] -> a -> b
getIso ((a,b):iso) x 
    | x == a     = b
    | otherwise  = getIso iso x

-- Given a spoilers play come up with the duplicators 
-- This uses the strategy given on page 29 of Libkin
-- Pre: length lin1,lin2 >= 2^k
--      length spoil <= k
strategy :: (Graph a, Graph b, GraphExtras a, GraphExtras b, Eq (Vertex a), Eq (Vertex b)) 
                        => Int -> a -> b -> [Vertex a] -> [Vertex b]
strategy k glin1 glin2 spoil = map (getIso iso) spoil
    where lin1 = graphToLin glin1
          lin2 = graphToLin glin2
          iso  = f k lin1 lin2 spoil

inIso :: Eq a => a -> [(a,b)] -> Bool
inIso x []    = False
inIso x ((a,b):ps)
    | x==a      = True 
    | otherwise = inIso x ps

f :: Eq a => Int -> [a] -> [b] -> [a] -> [(a,b)]
f _ _ _ [] = []
f 0 _ _ _  = []
f k lin1 lin2 (p:ps)
    | inIso p iso = iso
    | otherwise   = (p,chooseb k lin1 lin2 p) : iso
      where iso   = f (k-1) lin1 lin2 ps


-- This is the function that given an 'a' in lin1 finds a 'b' in lin2 s.t. lin1 - a =_(k-1) lin2 - b
chooseb :: Eq a => Int -> [a] -> [b] -> a -> b
chooseb k lin1 lin2 a
    | length lin1LT < 2^(k-1) = lin2 !! index a lin1
    | length lin1GT < 2^(k-1) = lin2 !! index a lin1
    | otherwise               = lin2 !! (2^(k-1)) -- proper way to do it would be split
    where (lin1LT,lin1GT) = split a lin1



strategy2 :: (Graph a, Graph b, GraphExtras a, GraphExtras b, Eq (Vertex a), Eq (Vertex b)) 
                        => Int -> a -> b -> [Vertex a] -> [Vertex b]
strategy2 k glin1 glin2 spoil = map (getIso iso) spoil
    where lin1 = graphToLin glin1
          lin2 = graphToLin glin2
          iso  = f2 k lin1 lin2 spoil []


-- Plan:
-- Keep the iso in the argument and pass it around, if somethings already in the iso then we can continue on to the next
-- spoiler play. If not then for the first two cases we want to zip together the appropriate parts of the list, add them 
-- to the iso and if the spoiler plays something not in the iso, call f2 on the remaining bit. It may seem strange that there
-- will be points on recursive calls of f2 that the spoiler can play outside lin1 but in that case it should be in iso.
f2 :: (Eq a, Eq b) => Int -> [a] -> [b] -> [a] -> [(a,b)] -> [(a,b)]
f2 _ _ _ [] iso = iso
f2 0 _ _ _  iso = iso
f2 k lin1 lin2 (a:ps) iso
    | inIso a iso             = f2 (k-1) lin1 lin2 ps iso
    | length lin1LT < 2^(k-1) = f2 (k-1) lin1GT lin2GTc1 ps (iso ++ zip lin1LT lin2LTc1)
    | length lin1GT < 2^(k-1) = f2 (k-1) lin1LT lin2LTc2 ps (iso ++ zip lin1GT lin2GTc2) -- doesnt matter that they're not reversed since they should be same size
    | otherwise               = lemma (k-1) (lin1LT,lin1GT) (lin2LTc3,lin2GTc3) ps ((a,bc3):iso)
      where (lin1LT,lin1GT)     = split a lin1
            (lin2LTc1,lin2GTc1) = splitAtD (index a lin1) lin2
            (lin2GTc2,lin2LTc2) = both reverse (splitAtD (length lin1 - index a lin1) (reverse lin2))
            (lin2LTc3,lin2GTc3) = splitAtD (2^(k-1)) lin2 -- check this has 2^k-1 elems
            bc3                 = lin2 !! (2^(k-1))

lemma :: (Eq a, Eq b) => Int -> ([a], [a]) -> ([b], [b]) -> [a] -> [(a, b)] -> [(a, b)]
lemma k (lin11,lin12) (lin21,lin22) ps iso = nub $ f2 k lin11 lin21 p1 iso ++ f2 k lin12 lin22 p2 iso
    where (p1,p2) = partition (flip elem lin11) ps

both :: (a -> b) -> (a, a) -> (b, b)
both f (x,y) = (f x, f y)


buildMorphEFkAtoB :: (Graph a, Graph b, GraphExtras a, GraphExtras b, Eq (Vertex a), Eq (Vertex b), Ord (Vertex a), Ord a)
                => Int -> a -> b -> GraphMorphism (EF a) b
buildMorphEFkAtoB k glin1 glin2 = GM (last Prelude.. strategy2 k glin1 glin2)


-- checkEFkMorph :: (GraphExtras a, Graph a, Graph b, Eq (Vertex b), Eq (Vertex a)) => Int -> a -> b -> b
-- checkEFkMorph k glin1 glin2 = apply (buildMorphEFkAtoB k glin1 glin2) eflin1
--     where eflin1 = graphToEFk k glin1


checkEFkMorph :: (Ord a, Ord b) => Int -> AdjacencyMap a -> AdjacencyMap b -> AdjacencyMap b
checkEFkMorph k glin1 glin2 = applyEF (buildMorphEFkAtoB k glin1 glin2) eflin1
    where eflin1 = graphToEFk k glin1


lin1 :: AdjacencyMap Integer
lin1 = linToGraph [1..17]
lin2 = linToGraph [3..22]

lin3 = linToGraph [1,2,3]

lin4 = linToGraph [1..9]
lin5 = linToGraph [4..12]

lin6 = linToGraph [1..4]
lin7 = linToGraph [5..8]
res2 = checkEFkMorph 2 lin6 lin7

res3 = checkMorphIsHomo (eftoAdjMap (graphToEFk 2 lin4)) lin5 (buildMorphEFkAtoB 2 lin4 lin5)
res4 = checkMorphIsHomo (eftoAdjMap (graphToEFk 4 lin1)) lin2 (buildMorphEFkAtoB 4 lin1 lin2)


------------------ Tree depth experiments  -------------------- 

data Gaifman a where Gaifman :: (Graph a, Ord a, Ord (Vertex a)) => AdjacencyMap (Vertex a) -> Gaifman a

-- The gaifman graph is undirected and irreflexive (no self edges)
-- Technically I think the Gaifman graph should include all elems of the universe, i.e. the type but this
-- would not be practical
getGaifmanGraph :: Ord a => AdjacencyMap a -> Gaifman (AdjacencyMap a)
getGaifmanGraph g = Gaifman $ AdjMap.edges (nub (concat [[(v1,v2),(v2,v1)] |(v1,v2) <- (edgeList g), v1 /= v2]))

-- Get connected componants of a Gaifman graph
getCC :: Gaifman (AdjacencyMap a) -> [Gaifman (AdjacencyMap a)]
getCC (Gaifman g) = map (Gaifman Prelude.. NonEmptyAdjMap.fromNonEmpty) $ vertexList $ scc g

-- Tree depth decomposition of the Gaifman graph


-- This applies the following method for treedepth decomposition to each connected componant
-- of gg.
-- A treedepth decomposition of a connected graph G=(V,E) is a rooted tree T=(V,ET) that
-- can be obtained in the following recursive procedure. If G has one vertex, then T=G.
-- Otherwise pick a vertex v∈V as the root of T, build a treedepth decomposition of each
-- connected component of G−v and add each of these decompositions to T by making its root
-- adjacent to v
gaifmanTDD :: Gaifman (AdjacencyMap a) -> [Tree a]
gaifmanTDD gg = map f (getCC gg)
    where f (Gaifman g)
            | vertexCount g == 1 = Node (head (vertexList g)) []
            | otherwise          = Node v (map f cc)
                where v  = head (vertexList g)
                      cc = getCC (Gaifman (removeVertex v g))


deriving instance (Graph a, Ord a, Ord (Vertex a), Show (Vertex a)) => Show (Gaifman a)    

------------------ Coalgebra to forest cover  -------------------- 
-- We assume that the coalgebra takes elems of the universe not in any relation (edge) to their singleton list
-- We then do not include them in the forest cover, since this would be impracticle.

-- Send each element to the list of its predecessors in the tree
forestToCoalg :: (Eq a, Ord a) => Forest a -> GraphMorphism (AdjacencyMap a) (EF (AdjacencyMap a))
forestToCoalg forest = (GM f)
    where f a = head $ mapMaybe (findNodePreds a) forest

-- Pre: The node a occurs only once in the tree
findNodePreds :: Eq a => a -> Tree a -> Maybe [a]
findNodePreds a t
    | rootLabel t == a  = Just [a]
    | subForest t == [] = Nothing
    | otherwise         = if null levelBelow then Nothing else Just $ (rootLabel t) : (head levelBelow)
      where levelBelow  = mapMaybe (findNodePreds a) (subForest t)

-- We also need the domain graph of the coalg to work out which elems of the universe are in edges so we can
-- apply the coalg to them to get the forest
coalgToForest :: (Eq a, Ord a) => GraphMorphism (AdjacencyMap a) (EF (AdjacencyMap a)) -> (AdjacencyMap a) -> Forest a
coalgToForest (GM f) g = foldr addToForest [] (foldr h [] (getVertices g))
    where h a l = updateList (f a) l
          updateList as []     = [as]
          updateList as (xs:xss)
            | isPrefixOf as xs = xs:xss
            | isPrefixOf xs as = as:xss
            | otherwise        = xs:(updateList as xss)
          buildForest p forest = forest

-- Doesnt work for empty lists since you cant have an empty tree
listToTree :: [a] -> Tree a
listToTree [x]     = Node x []
listToTree (x:xs)  = Node x [listToTree xs]

-- start with line tree, with each new tree its prefix closed so it needs to start at the root, follow down from root 
-- until we have to branch off, then add on the branch
-- if the roots dont match then can be part of same play so must be seperate forest

addToForest :: Eq a => [a] -> Forest a -> Forest a
addToForest [] []    = []
addToForest p []     = [listToTree p]
addToForest p (t:ts) = if rootLabel t == head p then nt:ts else t:addToForest p ts
    where nt = mergeWithTree t p

-- Pre: x == p, (x=rootLable tx)
mergeWithTree :: Eq a => Tree a -> [a] -> Tree a
mergeWithTree tx [p]             = tx
mergeWithTree (Node x xs) (p:ps) = f (checkNextLevel xs (head ps))
    where f (Just t, ts) = Node x ((mergeWithTree t ps):ts)
          f (Nothing,ts) = Node x ((listToTree ps):ts)

checkNextLevel :: Eq a => [Tree a] -> a -> (Maybe (Tree a), [Tree a])
checkNextLevel [] a     = (Nothing,[])
checkNextLevel (x:xs) a = if rootLabel x == a then (Just x,ts) else (Nothing,x:ts)
    where (t,ts) = checkNextLevel xs a

testCoalgForest g = coalgToForest (forestToCoalg gg) g == gg
    where gg = gaifmanTDD (getGaifmanGraph g)

getTreeDepthOfDecomp :: [Tree a] -> Int
getTreeDepthOfDecomp f = maximum (map (foldTree (\_ xs -> if null xs then 1 else 1 + maximum xs)) f)

res5 g = checkValidEFkGraph (getTreeDepthOfDecomp gg) g (gmap f g)
    where gg = gaifmanTDD (getGaifmanGraph g)
          (GM f) = forestToCoalg gg


res6 g = gmap f g
    where gg = gaifmanTDD (getGaifmanGraph g)
          (GM f) = forestToCoalg gg

test1 = linToGraph ["a","b","c","d"]
test2 = linToGraph ["d","e","f","a"]
o = AdjMap.overlay test1 test2
gg = gaifmanTDD (getGaifmanGraph $ o)