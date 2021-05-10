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

------------------ Proof of concept example with two equivilent graphs  -------------------- 
-- With EF comonad I can only prove them equivilent in fragment of logic with quantifier rank k.
-- To do this we give a coklislie morphism that takes the EK graph with play length k to graph b

-- Not acctually random, but generates arbitrary graphs given a seed
randomGraph :: Int -> Int -> AdjacencyMap Int
randomGraph seed n = fromAdjacencySets $ f verts nums
    where nums :: [Int]
          nums       = take (n*n) (randomRs (1, 2) (mkStdGen seed))
          verts      = [1..n]
          f [] r     = []
          f (v:vs) r = (v, Set.fromList [y |(x,y)<- zip rands verts, x==1]) : (f vs newr)
                        where (rands,newr) = splitAt n r

-- randomGraphList size num = map (\x -> randomGraph (mkStdGen x) size) [1..num]

liftMapToEFMorph ::(Graph a, Graph b, Ord (Vertex a), Ord a) => (Vertex a -> Vertex b) -> CoKleisli EF GraphMorphism a b
liftMapToEFMorph f = CoKleisli $ GM f Category.. counit

-- Proof that two isomorphic graphs are equal in the fragment quantifier rank k with counting quantifiers
-- Provide any valid iso (A->B, B->A)
proof1 :: Int -> Int -> Int -> (Int -> Int, Int -> Int) -> Bool
proof1 seed size k iso = eqQRankKCounting k g1tog2 g2tog1 graph1 graph2
    where graph1 = randomGraph seed size
          graph2 = gmap (fst iso) graph1
          g1tog2 = liftMapToEFMorph (fst iso)
          g2tog1 = liftMapToEFMorph (snd iso)

ex1 = proof1 45 3 4 ((\x -> x*2), (\x -> x `div` 2))

-- Proof that two isomorphic graphs are equal in the exisential positvie fragment with quantifier rank k
proof2 seed size k iso = eqQRankKEPfrag k g1tog2 g2tog1 graph1 graph2
    where graph1 = randomGraph seed size
          graph2 = gmap (fst iso) graph1
          g1tog2 = liftMapToEFMorph (fst iso)
          g2tog1 = liftMapToEFMorph (snd iso)

ex2 = proof2 45 3 4 ((\x -> x*2), (\x -> x `div` 2))
------------------ Example with linear orderings  --------------------
-- Given a list representing a linear ordering it returns the equivilent
-- graph with the edge relation interpreted as the < relation
linToGraph :: Ord a => [a] -> AdjacencyMap a
linToGraph xs = AdjMap.edges (f xs)
  where f [] = []
        f (x:xs) = map (\y -> (x,y)) xs ++ f xs

-- Counts occurrences of x in a list
count :: Eq a => a -> [a] -> Int
count x = foldr (\y xs-> if x==y then xs + 1 else xs) 0

-- converts a graph to a linear order
-- Pre: Graph is a representation of a lin order
graphToLin :: (GraphCoerce a, Eq (Vertex a)) => a -> [Vertex a]
graphToLin g = reverse $ map fst $ sortBy (\(_,a) (_,b) -> compare a b) $ map (\x -> (x,count x e)) (gvertices g)
    where e = map fst (edgeList (gcoerce g))

-- Splits the list into two parts on x with the middle element repeting
-- Pre: elem x xs
split :: Eq a => a -> [a] -> ([a],[a])
split x xs = f [] xs
    where f xs (y:ys) = if x == y then (reverse (x:xs), x:ys) else f (y:xs) ys

-- Splits the list into two parts at index i with middle element repeting
splitAtD :: Int -> [a] -> ([a],[a])
splitAtD i xs = (\(x,y) -> (x++[head y],y)) $ splitAt i xs

-- Get position of y in xs
-- Pre: y is in xs
index y xs = f xs 0
    where f (x:xs) i
            | x == y    = i
            | otherwise = f xs (i+1)

-- Like lookup but crashes if x isnt in the list
-- Pre: x is in the iso
getIso :: Eq a => [(a,b)] -> a -> b
getIso ((a,b):iso) x 
    | x == a     = b
    | otherwise  = getIso iso x

-- Check if x occurs as first elem in any of the pairs 
inIso :: Eq a => a -> [(a,b)] -> Bool
inIso x []    = False
inIso x ((a,b):ps)
    | x==a      = True 
    | otherwise = inIso x ps

both :: (a -> b) -> (a, a) -> (b, b)
both f (x,y) = (f x, f y)

-- Take two linear orders as graphs, and a spoilers play, return the duplicators play
-- Pre: Both the linear orders are at least length 2^k.
linStrategy :: (Graph a, Graph b, GraphCoerce a, GraphCoerce b, Eq (Vertex a), Eq (Vertex b)) 
                        => Int -> a -> b -> [Vertex a] -> [Vertex b]
linStrategy k glin1 glin2 spoil = map (getIso iso) spoil
    where lin1 = graphToLin glin1
          lin2 = graphToLin glin2
          iso  = linRec k lin1 lin2 spoil []

-- Recusivly implement the strategy
-- Plan:
-- Keep the iso in the argument and pass it around, if somethings already in the iso then we can continue on to the next
-- spoiler play. If not then for the first two cases we want to zip together the appropriate parts of the list, add them 
-- to the iso and if the spoiler plays something not in the iso, call linRec on the remaining bit. It may seem strange that
-- there will be points on recursive calls of linRec that the spoiler can play outside lin1 but in that case it should be in
-- iso.
linRec :: (Eq a, Eq b) => Int -> [a] -> [b] -> [a] -> [(a,b)] -> [(a,b)]
linRec _ _ _ [] iso = iso
linRec 0 _ _ _  iso = iso
linRec k lin1 lin2 (a:ps) iso
    | inIso a iso             = linRec (k-1) lin1 lin2 ps iso
    | length lin1LT < 2^(k-1) = linRec (k-1) lin1GT lin2GTc1 ps (iso ++ zip lin1LT lin2LTc1)
    | length lin1GT < 2^(k-1) = linRec (k-1) lin1LT lin2LTc2 ps (iso ++ zip lin1GT lin2GTc2)
    | otherwise               = lemma (k-1) (lin1LT,lin1GT) (lin2LTc3,lin2GTc3) ps ((a,bc3):iso)
      where (lin1LT,lin1GT)     = split a lin1
            (lin2LTc1,lin2GTc1) = splitAtD (index a lin1) lin2
            (lin2GTc2,lin2LTc2) = both reverse (splitAtD (length lin1 - index a lin1) (reverse lin2))
            (lin2LTc3,lin2GTc3) = splitAtD (2^(k-1)) lin2
            bc3                 = lin2 !! (2^(k-1))

-- The lemma from the proof
lemma :: (Eq a, Eq b) => Int -> ([a], [a]) -> ([b], [b]) -> [a] -> [(a, b)] -> [(a, b)]
lemma k (lin11,lin12) (lin21,lin22) ps iso = nub $ linRec k lin11 lin21 p1 iso ++ linRec k lin12 lin22 p2 iso
    where (p1,p2) = partition (flip elem lin11) ps


-- checkEFkMorph :: (Ord a, Ord b) => Int -> AdjacencyMap a -> AdjacencyMap b -> AdjacencyMap b
-- checkEFkMorph k glin1 glin2 = apply ((buildMorphFromStrat linStrategy) k glin1 glin2) eflin1
--     where eflin1 = graphToEFk k glin1


--res2 = checkEFkMorph 2 lin6 lin7

--res3 = checkMorphIsHomo (graphToEFk 2 lin4) lin5 (buildLinMorph 2 lin4 lin5)
--res4 = checkMorphIsHomo (graphToEFk 4 lin1) lin2 (buildLinMorph 4 lin1 lin2)


-- Would be good to abstract this to some "checkStrat" function but due to unification problems its not really possible
-- (applying buildMorph g1 g2, then buildMorph g2 g1 is not good for ghc)

-- Pre: the two linear orders are at least lenght 2^k
proof3 k lin1 lin2 = eqQRankKEPfrag k gm1 gm2 g1 g2
    where gm1 = buildMorphFromStrat linStrategy k g1 g2
          gm2 = buildMorphFromStrat linStrategy k g2 g1
          g1 = linToGraph lin1
          g2 = linToGraph lin2


-- Takes ages
proof4 = eqQRankKEPfrag k gm1 gm2 g1 g2
    where gm1 = buildMorphFromStrat linStrategy k g1 g2
          gm2 = buildMorphFromStrat linStrategy k g2 g1
          k = 4
          g1 = linToGraph [1..17]
          g2 = linToGraph [3..22]

------------------ Two colourability/Even/Connectivity  -------------------- 
-- We can get two undriected graphs, one thats a cycle of size (2^k)+1, and one thats made up of two cycles, both of size 2^k
-- Then for the k round EF game they are equal. Since the single cycle graph is 2 colourable, odd and connected and the two cycle
-- graph is even, unconnected and not 2-colourable showing that they're equal with eqQRankKEPfrag k constitues a proof that they're 
-- equal in the equivilent logic.
 
-- Function to generate the two graphs
generateCycleG :: Int -> (AdjacencyMap Int, AdjacencyMap Int)
generateCycleG k = (symmetricClosure (AdjMap.circuit [1..2^k+1]),
                    symmetricClosure (AdjMap.overlay (AdjMap.circuit [1..2^k]) (AdjMap.circuit [2^k+1..2^(k+1)])))

-- Duplicators strategy is to ensure that the distance between any two of her pebbles is either equal to the
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

-- Get all nodes i away from n on a cycle graph
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


-- getEFkMorphCyc :: (Show a, Show b, Ord a, Ord b) => Int -> AdjacencyMap a -> AdjacencyMap b -> AdjacencyMap b
-- getEFkMorphCyc k glin1 glin2 = apply (buildMorphFromStrat cycStrategy k glin1 glin2) eflin1
--      where eflin1 = graphToEFk k glin1


-- res7 = getEFkMorphCyc k g1 g2

-- res8 = checkMorphIsHomo (graphToEFk k g1) g2 (buildCycleMorph k g1 g2)

-- res11 :: EF (AdjacencyMap Int)
-- res11 = apply (GM ( k g1 g2)) (graphToEFk k g1)
res13 = checkMorphIsHomoDebug (graphToEFk k g1) g2 gm
    where (g2,g1) = generateCycleG k
          k = 5
          (CoKleisli gm) = buildMorphFromStrat cycStrategy k g1 g2

-- Takes ages if k is 4, fine for 2 and 3
proof5 k = eqQRankKEPfrag k gm1 gm2 g1 g2
    where gm1 = buildMorphFromStrat cycStrategy k g1 g2
          gm2 = buildMorphFromStrat cycStrategy k g2 g1
          (g1,g2) = generateCycleG k


------------------ Cycle and line graph (tree is not expressable) ------------------


------------------ Hamiltonian --------------------

-- This will constitue a proof that a hamiltonian graph is not axiomatisable with a finite number 
-- of variables in FO logic, i.e. ∀k ∃A,B ∀p (A∈S ∧ B not in S ∧ A ≡kp B)

-- Two graphs, the first has a hamiltonian cycle, the second does not
generateHamiltonianG :: Int -> (AdjacencyMap Int, AdjacencyMap Int)
generateHamiltonianG k = (symmetricClosure (AdjMap.biclique [1..k] [k+1..2*k]),
                          symmetricClosure (AdjMap.biclique [1..k] [k+1..(2*k+1)]))

-- Strategy is to pick any elem on the same side not already in iso, since there are always k or more on each side
-- and the nodes on a given side are indistingushable this is a winning strategy.
-- Only works on hamitolians generated with generateHamiltonianG

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


-- Haskell needs the type of counit explicitally to work out which comonad it should use the counit for
hamMorphs :: (Graph b, Graph a, Vertex a ~ Int, Vertex b ~ Int, Ord a, Ord b) =>
    Int -> (CoKleisli Pebble GraphMorphism a b,
            CoKleisli Pebble GraphMorphism b a)
hamMorphs k = (CoKleisli $ f Category.. GM (hamStrategy k),
               CoKleisli $ f Category.. GM (hamStrategy k))
    where f :: (Graph g, Ord g, Ord (Vertex g)) => GraphMorphism (Pebble g) g 
          f = counit

------------------ Tree depth experiments  -------------------- 

data Gaifman a where Gaifman :: (Graph a, Ord a, Ord (Vertex a)) => AdjacencyMap (Vertex a) -> Gaifman a

-- The gaifman graph is undirected and irreflexive (no self edges)
-- Technically I think the Gaifman graph should include all elems of the universe, i.e. the type but this
-- would not be practical
getGaifmanGraph :: Ord a => AdjacencyMap a -> Gaifman (AdjacencyMap a)
getGaifmanGraph g = Gaifman $ AdjMap.edges (nub (concat newedges))
    where newedges = [[(v1,v2),(v2,v1)] |(v1,v2) <- (edgeList g), v1 /= v2]
-- Get connected componants of a Gaifman graph
getCC :: Gaifman (AdjacencyMap a) -> [Gaifman (AdjacencyMap a)]
getCC (Gaifman g) = map (Gaifman Prelude.. NonEmptyAdjMap.fromNonEmpty) $ vertexList $ scc g

-- Tree depth decomposition of the Gaifman graph


-- This applies the following method for treedepth decomposition to each connected componant
-- of gg.
-- A treedepth decomposition of a connected graph G=(V,E) is a rooted tree T=(V,ET) that
-- can be obtained in the following recursive procedure. If G has one vertex, then T=G.
-- Otherwise pick a vertex v in V as the root of T, build a treedepth decomposition of each
-- connected component of G-v and add each of these decompositions to T by making its root
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
-- Find the predecsors of a node
findNodePreds :: Eq a => a -> Tree a -> Maybe [a]
findNodePreds a t
    | rootLabel t == a  = Just [a]
    | subForest t == [] = Nothing
    | otherwise         = if null levelBelow then Nothing else Just $ (rootLabel t) : (head levelBelow)
      where levelBelow  = mapMaybe (findNodePreds a) (subForest t)

-- We also need the domain graph of the coalg to work out which elems of the universe are in edges so we can
-- apply the coalg to them to get the forest
coalgToForest :: (GraphCoerce a, Eq (Vertex a), Ord (Vertex a)) => GraphMorphism a (EF a) -> a -> Forest (Vertex a)
coalgToForest (GM f) g = foldr addToForest [] (foldr h [] (vertexList (gcoerce g)))
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

-- Checks if a graph and its assosiated object form a valid EFk coalgebra 
checkValidCoalg :: (GraphCoerce a, Eq (Vertex a), Ord (Vertex a)) => GraphMorphism a (EF a) -> a -> Bool
checkValidCoalg gm g = checkValidTDD g (coalgToForest gm g)

-- Checks if a forest is a valid forest
checkValidTDD :: (GraphCoerce a, Eq (Vertex a), Ord (Vertex a)) => a -> Forest (Vertex a) -> Bool
checkValidTDD g forest = foldr (\(x,y) xs -> xs && or (map (checkAorD x y) forest)) True es
    where es = edgeList (gcoerce g)
        
-- returns true if x is a decendent or ancestor of y
checkAorD :: (Eq a) => a -> a -> Tree a -> Bool
checkAorD x y (Node l ts) 
    | x == l    = foldr (\z zs -> checkD y z || zs) False ts
    | y == l    = foldr (\z zs -> checkD x z || zs) False ts
    | otherwise = foldr (\z zs -> checkAorD x y z || zs) False ts

-- returns true if x is in the tree
checkD :: (Eq a) => a -> Tree a -> Bool
checkD x t = foldTree (\y ys -> if y == x then True else or ys) t

res5 g = checkValidEFkGraph (getTreeDepthOfDecomp gg) g (gmap f g)
    where gg = gaifmanTDD (getGaifmanGraph g)
          (GM f) = forestToCoalg gg

-- Gets tree decomposition then uses the coalgebra version of it as a graph morphism on g
res6 g = gmap f g
    where gg = gaifmanTDD (getGaifmanGraph g)
          (GM f) = forestToCoalg gg

-- Shows two graphs before and after overlay
showMerge t1 t2 = printGraphs $ [res6 t1, res6 t2, res6 o]
    where o = AdjMap.overlay t1 t2


test1 = linToGraph [1..4]
test2 = linToGraph [4,5,6,1]
o t1 t2 = AdjMap.overlay (linToGraph t1) (linToGraph t2)
gg o = gaifmanTDD (getGaifmanGraph $ o)
