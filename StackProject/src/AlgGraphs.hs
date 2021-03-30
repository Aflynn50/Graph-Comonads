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
import qualified Algebra.Graph.NonEmpty.AdjacencyMap as NonEmptyAdjMap (fromNonEmpty, overlay, edge, edgeList)
import Algebra.Graph.AdjacencyMap.Algorithm


import GHC.Exts (Constraint)
import Data.List
import Data.Maybe
import Data.Coerce
import Data.Tree
import Debug.Trace
import Category


-- EF comonad over graph using algebraic adjaceny map graphs. 

-- Invarients:
--    - Graphs should not have more than one of the same vertex

-- Possible problems
--    Getting edge map and going back to graph looses vertacies that arnt in edges, this is bad
--      I should get rid of the whole Graph class stuff, stick with Adj maps only
--    There are probably issues with taking the universe as the type. I think I'd like to change this.
--    E.g. that graph morphisms actually go from one family of graphs to another rather than a specific pair
--    Not sure how if explicit universes would actally improve this. 
--      I could take the universe as the set of verticies of the graph 
--    A graph homomorphism should be able to go between graphs with any set of verticies as long as it preserves
--    the edges with its vertex map

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
data EF a where EFdata :: (Graph a) => AdjacencyMap [Vertex a] -> EF a

eftoAdjMap :: Graph a => EF a -> AdjacencyMap [Vertex a]
eftoAdjMap (EFdata g) = g

deriving instance (Graph a, Ord a, Show a, Ord (Vertex a), Show (Vertex a)) => Show (EF a)    

-- We need the Ord here because the Graph instance for AdjMaps needs it
instance Ord a => GraphExtras (AdjacencyMap a) where
    getEdges = edgeList
    getVertices = vertexList

instance (Graph a, Ord a, Ord (Vertex a)) => Graph (EF a) where
    type Vertex (EF a) = [Vertex a]
    empty = EFdata AdjMap.empty
    vertex v = EFdata $ AdjMap.vertex v
    overlay (EFdata g1) (EFdata g2) = EFdata $ AdjMap.overlay g1 g2
    connect (EFdata g1) (EFdata g2) = EFdata $ AdjMap.connect g1 g2

instance (Graph a, Ord a, Ord (Vertex a)) => GraphExtras (EF a) where
    getEdges (EFdata g) = edgeList g
    getVertices (EFdata g) = vertexList g

instance CFunctor EF GraphMorphism GraphMorphism where
     funcMap (GM f) = GM (map f)

instance CComonad EF GraphMorphism where
    counit          = GM last -- the universe of EF is none empty lists so this is ok
    extend (GM f)   = GM $ map f Prelude.. (tail Prelude.. inits) 

data Product a b where Prod :: (Graph a, Graph b) => AdjacencyMap (Vertex a, Vertex b) -> Product a b

instance (Graph a, Graph b, Ord (Vertex a), Ord (Vertex b)) => Graph (Product a b) where
    type Vertex (Product a b) = (Vertex a, Vertex b)
    empty = Prod AdjMap.empty
    vertex v = Prod $ AdjMap.vertex v
    overlay (Prod g1) (Prod g2) = Prod $ AdjMap.overlay g1 g2
    connect (Prod g1) (Prod g2) = Prod $ AdjMap.connect g1 g2

instance (Graph a, Graph b, Ord (Vertex a), Ord (Vertex b)) => GraphExtras (Product a b) where
    getEdges (Prod g) = edgeList g
    getVertices (Prod g) = vertexList g

instance CBifunctor Product GraphMorphism GraphMorphism GraphMorphism where
  bifuncMap (GM gm1) (GM gm2) = GM (\(x,y) -> (gm1 x, gm2 y))

product :: (Ord a, Ord b) => AdjacencyMap a -> AdjacencyMap b -> Product (AdjacencyMap a) (AdjacencyMap b)
product g1 g2 = Prod $ box g1 g2


data Coproduct a b where Coprod :: (Graph a, Graph a) => AdjacencyMap (Either (Vertex a) (Vertex b)) -> Coproduct a b

instance (Graph a, Graph b, Ord (Vertex a), Ord (Vertex b)) => Graph (Coproduct a b) where
    type Vertex (Coproduct a b) = Either (Vertex a) (Vertex b)
    empty = Coprod AdjMap.empty
    vertex v = Coprod $ AdjMap.vertex v
    overlay (Coprod g1) (Coprod g2) = Coprod $ AdjMap.overlay g1 g2
    connect (Coprod g1) (Coprod g2) = Coprod $ AdjMap.connect g1 g2

instance (Graph a, Graph b, Ord (Vertex a), Ord (Vertex b)) => GraphExtras (Coproduct a b) where
    getEdges (Coprod g) = edgeList g
    getVertices (Coprod g) = vertexList g

instance CBifunctor Coproduct GraphMorphism GraphMorphism GraphMorphism where
  bifuncMap (GM gm1) (GM gm2) = GM g
    where g (Left x)  = Left $ gm1 x
          g (Right x) = Right $ gm2 x

coproduct :: (Ord a, Ord b) => AdjacencyMap a -> AdjacencyMap b -> Coproduct (AdjacencyMap a) (AdjacencyMap b)
coproduct g1 g2 = Coprod $ AdjMap.overlay (gmap Left g1) (gmap Right g2)

-- Gives the equiliser graph and its the equaliser morphism.
-- G -> A --> B
-- /\ /\  -->
-- | /      
-- Z
-- This finds all the vertacies in A for which all edges they are included in are preserved by f and g in B.
-- It then builds the subgraph of A, G that only includes these vertacies
-- Any vertacies not in an edge in A are also included in G despite the fact that a vertex with no edges doesnt mean
-- anything since we take the type to be the universe, this was done in case we change the representation. 
getEqualizer :: (Graph c, Graph d, Vertex c ~ a, Vertex d ~ b, Ord a, Eq a, Eq b) =>    
        AdjacencyMap a -> AdjacencyMap b -> GraphMorphism c d -> GraphMorphism c d -> (AdjacencyMap a, GraphMorphism c c)
getEqualizer g1 g2 (GM gm1) (GM gm2) = (AdjMap.overlay (AdjMap.edges keptE) (AdjMap.vertices disjointV), GM Prelude.id)
    where vinE      = nub (concatMap (\(x,y) -> [x,y]) (edgeList g1))
          keptV     = map fst (intersect (map (\x -> (x,gm1 x)) vinE) (map (\x -> (x,gm2 x)) vinE))
          disjointV = filter (\x -> not (elem x keptV)) (vertexList g1)
          keptE     = filter (\(x,y)-> elem x keptV && elem y keptV) (edgeList g1)


-- apply :: (Graph a, Graph b, GraphExtras a, c ~ Vertex b) => GraphMorphism a b -> a -> AdjacencyMap c
-- apply (GM gm) g = AdjMap.edges (map (\(x,y) -> (gm x,gm y)) (getEdges g))

checkMorphIsHomo :: (Graph c, Graph d, Vertex c ~ a, Vertex d ~ b, Eq b) => AdjacencyMap a -> AdjacencyMap b -> GraphMorphism c d -> Bool
checkMorphIsHomo g1 g2 (GM gm) = foldr (\e b -> elem e eG2 && b) True eMapped
    where eMapped = map (\(x,y) -> (gm x,gm y)) (edgeList g1)
          eG2     = edgeList g2

------------------ Example with two equivilent graphs  -------------------- 
-- With EF comonad I can only prove them equivilent in fragment of logic with quantifier rank k.
-- To do this we give a coklislie morphism that takes the EK graph with play length k to graph b
graph1 :: AdjacencyMap Int
graph1 = AdjMap.edges [(1,2),(2,3)]

graph2 :: AdjacencyMap Char
graph2 = AdjMap.edges [('a','b'),('b','c')]

-- universe of a graph
universe :: (GraphExtras a, Eq (Vertex a)) => a -> [Vertex a]
universe = nub Prelude.. getVertices


-- Code to generate all compatible plays with a graph with universe uni.
-- The idea is to generate all k length permutations where every elem of uni occours at least once
-- Not very nice/efficient code but appears to work
-- suffixes gets all possible ascending orderings of k-len(uni) elems of the universe
-- Pre: k > length uni
plays :: Eq a => Int -> [a] -> [[a]]
plays k uni = nub $ concatMap permutations (map (uni++) suffixes)
    where suffixes = map tail (f r uni)
          r = k - (length uni) + 1
          f 1 uni = map (\x -> [x]) uni
          f i uni = nub $ concat [map ((head uni):) ps|ps <- 
            (map (f (i-1)) ((init Prelude.. tails) uni))]

-- Doesn't behave properly for k > length uni, it only returns lists of length k not all less than
plays1 :: Eq a => Int -> [a] -> [[a]]
plays1 k uni
    | length uni < k = f (k-(length uni)) (permutations uni)
    | otherwise       = concatMap (lengthksublists uni) [1..k]
        where f 0 xs = xs
              f i xs = nub $ concatMap (\x -> concatMap (allinserts x) pf) uni
                        where pf = (f (i-1) xs)

allinserts x []     = [[x]]
allinserts x (y:ys) = (x:y:ys) : map (y:) (allinserts x ys)

lengthksublists :: [a] -> Int -> [[a]]
lengthksublists xs 0 = [[]]
lengthksublists xs k = concatMap f (elemPairs xs)
    where f (x,ys) = map (x:) (lengthksublists ys (k-1))


elemPairs :: [a] -> [(a, [a])]
elemPairs []     = []
elemPairs (x:xs) = (x,xs) : (map (\(y,ys) -> (y,x:ys)) (elemPairs xs))



--isPlayCompatible :: (GraphExtras a, Eq (Vertex a)) => a -> [Vertex a] -> Bool
--isPlayCompatible g p = foldr (\x b -> (elem x p) && b) True (getVertices g)

-- Performs the action of the EFk functor
graphToEFk :: (GraphExtras a, Eq (Vertex a), Ord (Vertex a)) => Int -> a -> EF a
graphToEFk k g = EFdata $ AdjMap.edges $
    concatMap (\p -> mapMaybe (\e -> f e p) edgesOfg) ps
    where edgesOfg  = getEdges g
          ps        = plays1 k (universe g)
          f (a,b) p = maybePair (getPrefix p a, getPrefix p b)
                     
maybePair :: (Maybe a, Maybe b) -> Maybe (a, b)
maybePair (Just a, Just b) = Just (a,b)
maybePair _ = Nothing

-- get prefix of play ending in y
getPrefix :: Eq t => [t] -> t -> Maybe [t]
getPrefix [] _ = Nothing 
getPrefix (x:xs) y  
            | x==y      = Just [x]
            | otherwise =  f (getPrefix xs y)
                where f (Just r) = Just (x:r)
                      f Nothing  = Nothing

-- graphToEFk usually gives a massive graph so this allows a smaller version of it
graphToLimEFk :: (GraphExtras a, Eq (Vertex a), Ord (Vertex a)) => Int -> Int -> a -> EF a
graphToLimEFk lim k g = EFdata $ AdjMap.edges $
    concat $ take lim $ map (\p -> map (\(x,y) -> (f p x, f p y)) edgesOfg) ps
    where edgesOfg = getEdges g
          ps       = plays k (universe g)
          f (x:xs) y  -- get prefix of play ending in y
            | x==y      = [x]
            | otherwise = x:(f xs y)


-- This doesnt really make sense as a thing. The EF comonad should probably map each vertex
-- to all plays ending in that vertex, and the edges acordingly to that. Then when the 
-- EF a -> b morphism was applied we would get to a graph with a load of duplicate edges.
-- If we removed these we should get the graph b. This would probably actually be what we want.

-- It actually does make sense. A coalgebra (which is what this is) needs to map to a prefix closed
-- subset of A^(>=k). I.e. some particular play and its prefixes. This is given by the coalgebra
-- conditions.  If it doesn't preserve all edges its invalid becuase its not a homomorphism
-- Look at page 23 or struct and power
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


checkValidEFkGraph :: (Eq (Vertex g1), GraphExtras g1, GraphExtras g2, Vertex g2 ~ [Vertex g1]) => Int -> g1 -> g2 -> Bool
checkValidEFkGraph k g efg = foldr f True (getEdges efg)
    where gedges      = getEdges g
          f (xs,ys) b = length xs <= k && length ys <= k
                        && elem (last xs,last ys) gedges
                        && (isPrefixOf xs ys || isPrefixOf ys xs)
                        && b



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

applyEF :: (Eq b, Ord a, Ord b) => GraphMorphism (EF (AdjacencyMap a)) (AdjacencyMap b) -> (EF (AdjacencyMap a)) -> AdjacencyMap b
applyEF (GM gm) (EFdata g) = gmap gm g

-- Checks that there is a valid homomorphism from EF A -> B and EF B -> A. This is the condition
-- for equality up to quantifier rank k
eqUpToQuantRankK :: (Eq b, Ord a, Ord b) => Int -> GraphMorphism (EF (AdjacencyMap a)) (AdjacencyMap b) -> 
    GraphMorphism (EF (AdjacencyMap b)) (AdjacencyMap a) -> AdjacencyMap a -> AdjacencyMap b -> Bool
eqUpToQuantRankK k h1 h2 g1 g2 = (applyEF h1 (graphToEFk k g1) == g2) && (applyEF h2 (graphToEFk k g2) == g1)

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
f2 :: Eq a => Int -> [a] -> [b] -> [a] -> [(a,b)] -> [(a,b)]
f2 _ _ _ [] iso = iso
f2 0 _ _ _  iso = iso
f2 k lin1 lin2 (a:ps) iso
    | inIso a iso             = f2 (k-1) lin1 lin2 ps iso
    | length lin1LT < 2^(k-1) = f2 (k-1) lin1GT lin2GTc1 ps (iso ++ zip lin1LT lin2LTc1)
    | length lin1GT < 2^(k-1) = f2 (k-1) lin1LT lin2LTc2 ps (iso ++ zip lin1GT lin2GTc2) -- doesnt matter that they're not reversed since they should be same size
    | otherwise               = lemma (k-1) (lin1LT,lin1GT) (lin2LTc3,lin2LTc3) ps ((a,bc3):iso)
      where (lin1LT,lin1GT)     = split a lin1
            (lin2LTc1,lin2GTc1) = splitAtD (index a lin1) lin2
            (lin2GTc2,lin2LTc2) = both reverse (splitAtD (length lin1 - index a lin1) (reverse lin2))
            (lin2LTc3,lin2GTc3) = splitAtD (2^(k-1)) lin2 -- check this has 2^k-1 elems
            bc3                 = lin2 !! (2^(k-1))

lemma :: Eq a => Int -> ([a], [a]) -> ([b], [b]) -> [a] -> [(a, b)] -> [(a, b)]
lemma k (lin11,lin12) (lin21,lin22) ps iso = f2 k lin11 lin21 p1 iso ++ f2 k lin12 lin22 p2 iso
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

res3 = checkMorphIsHomo (eftoAdjMap (graphToEFk 2 lin6)) lin7 (buildMorphEFkAtoB 2 lin6 lin7)


------------------ Tree depth experiments  -------------------- 

data Gaifman a where Gaifman :: (Graph a, Ord a, Ord (Vertex a)) => AdjacencyMap (Vertex a) -> Gaifman a

-- The gaifman graph is undirected and irreflexive (no self edges)
getGaifmanGraph :: Ord a => AdjacencyMap a -> Gaifman (AdjacencyMap a)
getGaifmanGraph g = Gaifman $ AdjMap.edges (nub (concat [[(v1,v2),(v2,v1)] |(v1,v2) <- (edgeList g), v1 /= v2]))

-- Get connected componants of a Gaifman graph
getCC :: Gaifman (AdjacencyMap a) -> [Gaifman (AdjacencyMap a)]
getCC (Gaifman g) = map (Gaifman Prelude.. NonEmptyAdjMap.fromNonEmpty) $ vertexList $ scc g

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

