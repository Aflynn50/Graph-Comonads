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
import Data.Map as Map (Map, fromList, insert, toList, empty, lookup, elems)
import Data.Set as Set (Set, fromList)
import System.Random hiding (split)
import Debug.Trace
import Category
import AlgGraphsCat 
import DrawGraphs

------------------ Example with two equivilent graphs  -------------------- 
-- With EF comonad I can only prove them equivilent in fragment of logic with quantifier rank k.
-- To do this we give a coklislie morphism that takes the EK graph with play length k to graph b
graph1 :: AdjacencyMap Int
graph1 = AdjMap.edges [(1,2),(2,3)]

graph2 :: AdjacencyMap Char
graph2 = AdjMap.edges [('a','b'),('b','c')]

liftMapToEFMorph ::(Graph a, Graph b, Ord (Vertex a), Ord a) => (Vertex a -> Vertex b) -> GraphMorphism (EF a) b
liftMapToEFMorph f = GM f Category.. counit

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
graphToLin :: (Graph a, GraphCoerce a, Eq (Vertex a)) => a -> [Vertex a]
graphToLin g = reverse $ map fst $ sortBy (\(_,a) (_,b) -> compare a b) $ map (\x -> (x,count x e)) (universe g)
    where e = map fst (edgeList (gcoerce g))

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

strategy2 :: (Graph a, Graph b, GraphCoerce a, GraphCoerce b, Eq (Vertex a), Eq (Vertex b)) 
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

inIso :: Eq a => a -> [(a,b)] -> Bool
inIso x []    = False
inIso x ((a,b):ps)
    | x==a      = True 
    | otherwise = inIso x ps


lemma :: (Eq a, Eq b) => Int -> ([a], [a]) -> ([b], [b]) -> [a] -> [(a, b)] -> [(a, b)]
lemma k (lin11,lin12) (lin21,lin22) ps iso = nub $ f2 k lin11 lin21 p1 iso ++ f2 k lin12 lin22 p2 iso
    where (p1,p2) = partition (flip elem lin11) ps

both :: (a -> b) -> (a, a) -> (b, b)
both f (x,y) = (f x, f y)



-- Builds the morphism f: EFk(A) -> B
buildLinMorph :: (Graph a, Graph b, GraphCoerce a, GraphCoerce b, Eq (Vertex a), Eq (Vertex b), Ord (Vertex a), Ord a)
                => Int -> a -> b -> GraphMorphism (EF a) b
buildLinMorph k glin1 glin2 = GM (last Prelude.. strategy2 k glin1 glin2)


checkEFkMorph :: (Ord a, Ord b) => Int -> AdjacencyMap a -> AdjacencyMap b -> AdjacencyMap b
checkEFkMorph k glin1 glin2 = apply (buildLinMorph k glin1 glin2) eflin1
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

res3 = checkMorphIsHomo (gcoerce (graphToEFk 2 lin4)) lin5 (buildLinMorph 2 lin4 lin5)
res4 = checkMorphIsHomo (gcoerce (graphToEFk 4 lin1)) lin2 (buildLinMorph 4 lin1 lin2)

------------------ Two colourability/Even/Connectivity  -------------------- 
-- Does this need to be the symetric closure of the graphs?
generateCycleG :: Int -> (AdjacencyMap Int, AdjacencyMap Int)
generateCycleG k = (symmetricClosure (AdjMap.circuit [1..2^k+1]),
                    symmetricClosure (AdjMap.overlay (AdjMap.circuit [1..2^k]) (AdjMap.circuit [2^k+1..2^(k+1)])))

-- Duplicators strategy is to ensure that the distance between any two of her pebbles is either the equal to the
-- distance between the corrosponding pair of the spoilers pebbles, or, it is greater than 2^k-r. If the two spoilers
-- pebbels are on the same graph then it needs to be equal, otherwise greater than 2^k
-- Spoil plays in g1
cycStrategy :: (Show (Vertex a), Show (Vertex b), Graph a, Graph b, GraphCoerce a, GraphCoerce b, Ord (Vertex a), Ord (Vertex b)) 
                    => Int -> a -> b -> [Vertex a] -> [Vertex b]
cycStrategy k g1 g2 spoil = f spoil [] [] 1
    where f []     ss ds r = ds
          f (x:xs) ss ds r = f xs (ss++[x]) (ds++[g (findEqualPlacing x (gcoerce g1) (gcoerce g2) ss ds)]) (r+1)
            where g (Just y) = y
                  g Nothing  = findFarPlacing k r x (gcoerce g1) (gcoerce g2) ss ds

-- Remove all elems of xs from ys
removeL :: Eq a => [a] -> [a] -> [a]
removeL xs ys = filter (\y -> not (elem y xs)) ys

-- Find a placing in g2 of distance 2^(k-r) away from all others, if it is the last node to be places, make sure it
-- respects adjancecy since it will be of dist 1 away
findFarPlacing :: (Eq a, Ord a, Ord b) => Int -> Int -> a -> AdjacencyMap a -> AdjacencyMap b -> [a] -> [b] -> b
findFarPlacing k r n g1 g2 spoil dup = if d==1 && t then head (intersect neighbours2 placings) else head placings
    where placings    = foldr (\x xs -> intersect (getGTIAway x d g2) xs) (vertexList g2) dup
          d           = 2^(k-r)
          t           = elem (last spoil) neighbours1
          neighbours1 = getIAway n 1 g1
          neighbours2 = getIAway (last dup) 1 g2

-- get closer nodes then take them away from whole graph
-- Get all nodes of distance i or larger from n in g
getGTIAway :: (Eq a, Ord a) => a -> Int -> AdjacencyMap a -> [a]
getGTIAway n i g = removeL (f 0 [] [n]) (vertexList g) 
    where f d visited []    = visited
          f d visited nodes 
            | d>=i      = visited
            | otherwise = f (d+1) newV newN
                where newN = concatMap (\x -> removeL newV (fromJust (Map.lookup x adjMap))) nodes
                      newV  = visited ++ nodes
          adjMap = Map.fromList (adjacencyList g ) 

-- Find placing of node on g2 s.t. it preserves the none-infinite distances to the nodes in g1
-- If this is impossible return Nothing.
-- Dup and spoil should be the same length
-- Go through nodes close to n in other graph and see if there are any positions you can place the new one that
-- Keep the distances
-- If the distances of all spoilers plays are Nothing then return Nothing
findEqualPlacing :: (Show a, Show b, Eq a, Ord a, Ord b) => a -> AdjacencyMap a -> AdjacencyMap b -> [a] -> [b] -> Maybe b
findEqualPlacing n g1 g2 spoil dup = if incomparableS then Nothing 
                                                else listToMaybe $ removeL dup $ foldr f g1Vlist (zip spoil dup) 
    where spoilDists   = getCycDistances n g1 spoil
          f (x,y) xs   = intersect (g y (fromJust (Map.lookup x spoilDists))) xs
          g y (Just d)   = getIAway y d g2
          g y Nothing    = g1Vlist
          incomparableS  = foldr (\x xs -> (x==Nothing) && xs) True (Map.elems spoilDists)
          g1Vlist      = vertexList g2


getIAway :: (Eq a, Ord a) => a -> Int -> AdjacencyMap a -> [a]
getIAway n i g = nub (f 0 [] [n])
    where f d visited []        = []
          f d visited nodes 
            | d==i      = nodes
            | otherwise = f (d+1) newV newN
                where newN = concatMap (\x -> removeL newV (fromJust (Map.lookup x adjMap))) nodes
                      newV  = visited ++ nodes
          adjMap = Map.fromList (adjacencyList g )
-- Given a node and a graph find the distance from it to each other node in spoil (Nothing if infinite)
-- Only works graphs that are a collection of cycles
-- Dists should be a map
getCycDistances :: (Show a, Eq a, Ord a) => a -> AdjacencyMap a -> [a] -> Map a (Maybe Int)
getCycDistances n g spoil = foldr (\x xs-> Map.insert x (Map.lookup x listOfDists) xs) Map.empty spoil 
    where listOfDists                 = f 0 [] [n] Map.empty
          f d visited [] dists        = dists
          f d visited nodes dists = f (d+1) newV newN newD
                where newN = concatMap (\x -> removeL newV (fromJust (Map.lookup x adjMap))) nodes
                      newD  = foldr (\x xs -> Map.insert x d xs) dists nodes
                      newV  = visited ++ nodes
          adjMap = Map.fromList (adjacencyList g)


buildCycleMorph :: (Show (Vertex a), Show (Vertex b), Graph a, Graph b, GraphCoerce a, GraphCoerce b, Ord a, Ord (Vertex a), Ord (Vertex b))
                => Int -> a -> b -> GraphMorphism (EF a) b
buildCycleMorph k glin1 glin2 = GM (last Prelude.. cycStrategy k glin1 glin2)




getEFkMorphCyc :: (Show a, Show b, Ord a, Ord b) => Int -> AdjacencyMap a -> AdjacencyMap b -> AdjacencyMap b
getEFkMorphCyc k glin1 glin2 = apply (buildMorphFromStrat cycStrategy k glin1 glin2) eflin1
     where eflin1 = graphToEFk k glin1

k = 3
(g1,g2) = generateCycleG k

res7 = getEFkMorphCyc k g1 g2

res8 = checkMorphIsHomo (gcoerce (graphToEFk k g1)) g2 (buildCycleMorph k g1 g2)

-- Playing on big
res9 l = cycStrategy k g1 g2 l

-- Playing on 2 small
res10 l = cycStrategy k g2 g1 l
-- res11 :: EF (AdjacencyMap Int)
-- res11 = apply (GM ( k g1 g2)) (graphToEFk k g1)
res12 = graphToEFk k g1
res13 = checkMorphIsHomoDebug (gcoerce (graphToEFk k g1)) g2 (buildCycleMorph k g1 g2)

------------------ Hamiltonian --------------------

-- This will constitue a proof that a hamiltonian graph is not axiomatisable with a finite number 
-- of variables in FO logic, i.e. ∀k ∃A,B ∀p (A∈S ∧ B not in S ∧ A ≡kp B)

-- I need to give the two graphs, then give the duplicators strategy

-- Two graphs, the first has a hamiltonian cycle, the second does not
generateHamiltonianG :: Int -> (AdjacencyMap Int, AdjacencyMap Int)
generateHamiltonianG k = (symmetricClosure (AdjMap.biclique [1..k] [k+1..2*k]),
                          symmetricClosure (AdjMap.biclique [1..k] [k+1..(2*k+1)]))

-- Strategy is to pick any elem on the same side not already in iso, since there are always k or more on each side
-- and the nodes on a given side are indistingushable this is a winning strategy.
-- Only works on hamitolians generated with generateHamiltonianG

-- I need to work out if I can use places that used to have a pebble on, I think I can?

--Basically choose an unused elem in the same side of the graph
hamStrategy :: Int -> [(Int,Int)] -> [(Int,Int)]
hamStrategy k spoil = hamStratRec k spoil []

-- find elems on one side of the graph that arnt currently in the iso, need to keep track of moved pebbles
unusedKLT :: Int -> [(Int,Int)] -> Int
unusedKLT k revdup = head (dropWhile (\x -> not (elem x usedNodes)) [1..k])
    where usedNodes = [a | (i,a) <- currentPos (reverse revdup),i<=k]

unusedKGT :: Int -> [(Int,Int)] -> Int
unusedKGT k revdup = head (dropWhile (\x -> not (elem x usedNodes)) [k+1..2*k+1])
    where usedNodes = [a | (i,a) <- currentPos (reverse revdup),i>k]

-- Given a play get the end position of all the pebbles (i.e. remove duplicate occurences of peb positions)
currentPos :: [(Int,a)] -> [(Int,a)]
currentPos ps = f ps Map.empty
    where f [] curpos         = Map.toList curpos
          f ((i,x):xs) curpos = f xs (Map.insert i x curpos)

-- revdup is the reverse of the duplicators play, i.e. if (1,a) occours before (1,b) in the list then
-- pebble 1 is on a  
hamStratRec :: Int -> [(Int,Int)] -> [(Int,Int)] -> [(Int,Int)]
hamStratRec k [] revdup = reverse revdup
hamStratRec k ((pi,n):xs) revdup 
    | n <= k     = hamStratRec k xs ((pi,unusedKLT k revdup):revdup)
    | otherwise  = hamStratRec k xs ((pi,unusedKGT k revdup):revdup)


-- elemInIso :: Eq a => a -> [(Int,b)] -> Bool
-- elemInIso x []    = False
-- elemInIso x ((i,a):ps)
--     | a==x      = True 
--     | otherwise = elemInIso x ps

-- pebInIso :: Eq a => Int -> [((Int,a),(Int,b))] -> Bool
-- pebInIso x []    = False
-- pebInIso x (((i,a),(j,b)):ps)
--     | j==x      = True 
--     | otherwise = inIso x ps



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
coalgToForest (GM f) g = foldr addToForest [] (foldr h [] (vertexList g))
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

showMerge t1 t2 = printGraphs $ [res6 t1, res6 t2, res6 o]
    where o = AdjMap.overlay t1 t2

randomGraph :: (RandomGen g) => g -> Int -> AdjacencyMap Int
randomGraph g n = fromAdjacencySets $ f verts nums
    where nums :: [Int]
          nums       = take (n*n) (randomRs (1, 2) g)
          verts      = [1..n]
          f [] r     = []
          f (v:vs) r = (v, Set.fromList [y|(x,y)<- zip rands verts, x==1]) : (f vs newr)
                where (rands,newr) = splitAt n r

-- Not acctually random
randomGraphList size num = map (\x -> randomGraph (mkStdGen x) size) [1..num]


test1 = linToGraph [1..4]
test2 = linToGraph [4,5,6,1]
o t1 t2 = AdjMap.overlay (linToGraph t1) (linToGraph t2)
gg o = gaifmanTDD (getGaifmanGraph $ o)