{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE TypeFamilies           #-} 
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE KindSignatures         #-}


module AlgGraphsCat where

import Algebra.Graph.Class
import Algebra.Graph.AdjacencyMap as AdjMap
import qualified Algebra.Graph.NonEmpty.AdjacencyMap as NonEmptyAdjMap (fromNonEmpty, overlay, edge, edgeList)
import Algebra.Graph.AdjacencyMap.Algorithm

import GHC.TypeLits
import GHC.TypeLits.Extra 
import GHC.Exts (Constraint)
import Data.List
import Data.Maybe
import Data.Coerce
import Data.Tree
import Data.Proxy
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
--    Not sure how if explicit universes would actally improve this - they would dissallow infinite universes
--      I could take the universe as the set of verticies of the graph 
--      A graph homomorphism should be able to go between graphs with any set of verticies as long as it preserves
--      the edges with its vertex map
--    The universe of EF and pebble should both be none empty lists
-- EF category


-- I could maybe change the EF and Peb datatypes to accept a graph that has graph coerce implemented
-- rather than just forcing it to be an AdjMap, then make gcoerce call down the stack, this would
-- allow stacking of functor actions

data GraphMorphism a b where GM :: (Graph a, Graph b) => (Vertex a -> Vertex b) -> GraphMorphism a b 

instance Category GraphMorphism where
    type Object GraphMorphism g = Graph g
    id          = GM Prelude.id
    GM f . GM g = GM (f Prelude.. g)

-- Needs to preserve the roots of the trees in the forest
data ForestMorphism a b where FM :: (Forest a -> Forest b) -> ForestMorphism a b 

class ForestCover f where
    type FVertex f
    getForest :: f -> Forest (FVertex f)

instance Category ForestMorphism where
    type Object ForestMorphism f = ForestCover f
    id          = FM Prelude.id 
    FM f . FM g = FM (f Prelude.. g)

-- I think this could probably be better done with coerce
-- Change this to a thing that has a function from g to adjmap and nothing else. 
class Graph g => GraphCoerce g where
    gcoerce    :: g -> AdjacencyMap (Vertex g)
    gcoerceRev :: AdjacencyMap (Vertex g) -> g

deriving instance (Graph a, Ord a, Show a, Ord (Vertex a), Show (Vertex a)) => Show (EF a)    

-- We need the Ord here because the Graph instance for AdjMaps needs it
instance Ord a => GraphCoerce (AdjacencyMap a) where
    gcoerce    = Prelude.id
    gcoerceRev = Prelude.id

------ The Ehrenfeucht-Fraı̈ssé Comonad ------
-- Should technically be non empty lists rather than just haskell lists

-- one of these two defns
-- data EF a where EFdata :: Graph [a] => a -> EFdata a
data EF a where EFdata :: (Graph a) => AdjacencyMap [Vertex a] -> EF a

instance (Graph a, Ord a, Ord (Vertex a)) => Graph (EF a) where
    type Vertex (EF a) = [Vertex a]
    empty = EFdata AdjMap.empty
    vertex v = EFdata $ AdjMap.vertex v
    overlay (EFdata g1) (EFdata g2) = EFdata $ AdjMap.overlay g1 g2
    connect (EFdata g1) (EFdata g2) = EFdata $ AdjMap.connect g1 g2

instance (Graph a, Ord a, Ord (Vertex a)) => GraphCoerce (EF a) where
    gcoerce (EFdata g) = g
    gcoerceRev g       = EFdata g 

instance CComonad EF GraphMorphism where
    counit          = GM last -- the universe of EF is none empty lists so this is ok
    extend (GM f)   = GM $ map f Prelude.. (tail Prelude.. inits) 

------ The Pebbling Comonad ------
-- Should technically be non empty lists rather than just haskell lists


data Pebble a where Peb :: (Graph a) => AdjacencyMap [(Int, Vertex a)] -> Pebble a

instance (Graph a, Ord a, Ord (Vertex a)) => Graph (Pebble a) where
    type Vertex (Pebble a) = [(Int,Vertex a)]
    empty = Peb AdjMap.empty
    vertex v = Peb $ AdjMap.vertex v
    overlay (Peb g1) (Peb g2) = Peb $ AdjMap.overlay g1 g2
    connect (Peb g1) (Peb g2) = Peb $ AdjMap.connect g1 g2

instance (Graph a, Ord a, Ord (Vertex a)) => GraphCoerce (Pebble a) where
    gcoerce (Peb g) = g
    gcoerceRev g    = Peb g 

instance CComonad Pebble GraphMorphism where
    counit          = GM $ snd Prelude.. last -- the universe of Pebbles is none empty lists so this is ok
    extend (GM f)   = GM $ map (\xs -> (fst (last xs),f xs)) Prelude.. (tail Prelude.. inits)

-- Modal comonad

-- Category functors

data Product a b where Prod :: (Graph a, Graph b) => AdjacencyMap (Vertex a, Vertex b) -> Product a b

instance (Graph a, Graph b, Ord (Vertex a), Ord (Vertex b)) => Graph (Product a b) where
    type Vertex (Product a b) = (Vertex a, Vertex b)
    empty = Prod AdjMap.empty
    vertex v = Prod $ AdjMap.vertex v
    overlay (Prod g1) (Prod g2) = Prod $ AdjMap.overlay g1 g2
    connect (Prod g1) (Prod g2) = Prod $ AdjMap.connect g1 g2

instance (Graph a, Graph b, Ord (Vertex a), Ord (Vertex b)) => GraphCoerce (Product a b) where
    gcoerce (Prod g) = g
    gcoerceRev g     = Prod g 

instance CBifunctor Product GraphMorphism GraphMorphism GraphMorphism where
  bifuncMap (GM gm1) (GM gm2) = GM (\(x,y) -> (gm1 x, gm2 y))

product :: (Ord a, Ord b) => AdjacencyMap a -> AdjacencyMap b -> Product (AdjacencyMap a) (AdjacencyMap b)
product g1 g2 = Prod $ box g1 g2


data Coproduct a b where Coprod :: (Graph a, Graph b) => AdjacencyMap (Either (Vertex a) (Vertex b)) -> Coproduct a b

instance (Graph a, Graph b, Ord (Vertex a), Ord (Vertex b)) => Graph (Coproduct a b) where
    type Vertex (Coproduct a b) = Either (Vertex a) (Vertex b)
    empty = Coprod AdjMap.empty
    vertex v = Coprod $ AdjMap.vertex v
    overlay (Coprod g1) (Coprod g2) = Coprod $ AdjMap.overlay g1 g2
    connect (Coprod g1) (Coprod g2) = Coprod $ AdjMap.connect g1 g2

instance (Graph a, Graph b, Ord (Vertex a), Ord (Vertex b)) => GraphCoerce (Coproduct a b) where
    gcoerce (Coprod g) = g
    gcoerceRev g       = Coprod g  

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


-- I should also do the coequaliser

-- getCoequalizer :: (Graph c, Graph d, Vertex c ~ a, Vertex d ~ b, Ord a, Eq a, Eq b) =>    
--         AdjacencyMap a -> AdjacencyMap b -> GraphMorphism c d -> GraphMorphism c d -> (AdjacencyMap a, GraphMorphism c c)
-- getCoequalizer g1 g2  

-- Useful functions

apply :: (Graph a, Graph b, GraphCoerce a, GraphCoerce b, Ord (Vertex a), Ord (Vertex b)) => GraphMorphism a b -> a -> b
apply (GM gm) g = gcoerceRev (gmap gm (gcoerce g))

-- change to use GraphCoerce
-- Check if each edge in g1 is mapped by gm to an edge in g2
checkMorphIsHomo :: (Graph c, Graph d, Vertex c ~ a, Vertex d ~ b, Eq b) => AdjacencyMap a -> AdjacencyMap b -> GraphMorphism c d -> Bool
checkMorphIsHomo g1 g2 (GM gm) = foldr (\e b -> elem e eG2 && b) True eMapped
    where eMapped = map (\(x,y) -> (gm x,gm y)) (edgeList g1)
          eG2     = edgeList g2

-- Get all edges in g1 (and their mappings under gm) that are not mapped to an edge in g2 by gm
checkMorphIsHomoDebug :: (Graph c, Graph d, Vertex c ~ a, Vertex d ~ b, Eq b) => AdjacencyMap a -> AdjacencyMap b -> GraphMorphism c d -> [((a,a),(b,b))]
checkMorphIsHomoDebug g1 g2 (GM gm) = [(e1,e2)| (e1,e2) <- eMapped,not (elem e2 eG2)]
    where eMapped = map (\(x,y) -> ((x,y),(gm x,gm y))) (edgeList g1)
          eG2     = edgeList g2

-- universe of a graph
universe :: (GraphCoerce a, Eq (Vertex a)) => a -> [Vertex a]
universe = nub Prelude.. vertexList Prelude.. gcoerce


-- -- Code to generate all compatible plays with a graph with universe uni.
-- -- The idea is to generate all k length permutations where every elem of uni occours at least once
-- -- Not very nice/efficient code but appears to work
-- -- suffixes gets all possible ascending orderings of k-len(uni) elems of the universe
-- -- Pre: k > length uni
-- plays :: Eq a => Int -> [a] -> [[a]]
-- plays k uni = nub $ concatMap permutations (map (uni++) suffixes)
--     where suffixes = map tail (f r uni)
--           r = k - (length uni) + 1
--           f 1 uni = map (\x -> [x]) uni
--           f i uni = nub $ concat [map ((head uni):) ps|ps <- 
--             (map (f (i-1)) ((init Prelude.. tails) uni))]

plays :: Eq a => Int -> [a] -> [[a]]
plays k uni
    | length uni < k = (plays (k-1) uni) ++ (f (k-(length uni)) (permutations uni))
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
graphToEFk :: (GraphCoerce a, Eq (Vertex a), Ord (Vertex a)) => Int -> a -> EF a
graphToEFk k g = EFdata $ AdjMap.edges $
    concatMap (\p -> mapMaybe (\e -> f e p) edgesOfg) ps
    where edgesOfg  = edgeList (gcoerce g)
          ps        = plays k (universe g)
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
graphToLimEFk :: (GraphCoerce a, Eq (Vertex a), Ord (Vertex a)) => Int -> Int -> a -> EF a
graphToLimEFk lim k g = EFdata $ AdjMap.edges $
    concat $ take lim $ map (\p -> map (\(x,y) -> (f p x, f p y)) edgesOfg) ps
    where edgesOfg = edgeList (gcoerce g)
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

checkValidEFkGraph :: (Eq (Vertex g1), GraphCoerce g1, GraphCoerce g2, Vertex g2 ~ [Vertex g1]) => Int -> g1 -> g2 -> Bool
checkValidEFkGraph k g efg = foldr f True (edgeList (gcoerce efg))
    where gedges      = edgeList (gcoerce g)
          f (xs,ys) b = length xs <= k && length ys <= k
                        && elem (last xs,last ys) gedges
                        && (isPrefixOf xs ys || isPrefixOf ys xs)
                        && b

checkValidPebkGraph :: (Eq (Vertex g1), Graph g1, Graph g2, GraphCoerce g1, GraphCoerce g2, Vertex g2 ~ [(Int,Vertex g1)]) => Int -> g1 -> g2 -> Bool
checkValidPebkGraph k g pebg = foldr f True (edgeList (gcoerce pebg))
    where gedges      = edgeList (gcoerce g)
          checkk xs   = foldr (\(x,y) b' -> b' && x <= k) True xs 
          f (xs,ys) b = checkk xs && checkk ys
                        && elem (snd (last xs),snd (last ys)) gedges
                        && g1 xs ys
                        && b
          g1 xs ys
            | isPrefixOf xs ys = h xs ys
            | isPrefixOf ys xs = h ys xs
            | otherwise        = False
                where h xs' ys' = foldr (\(x,_) b' -> (lastx /= x) && b') True (drop (length xs') ys') 
                        where lastx     = fst (last xs')



-- Checks that there is a valid homomorphism from EF A -> B and EF B -> A. This is the condition
-- for equality up to quantifier rank k
eqUpToQuantRankK :: (Eq b, Ord a, Ord b) => Int -> GraphMorphism (EF (AdjacencyMap a)) (AdjacencyMap b) -> 
    GraphMorphism (EF (AdjacencyMap b)) (AdjacencyMap a) -> AdjacencyMap a -> AdjacencyMap b -> Bool
eqUpToQuantRankK k h1 h2 g1 g2 = (apply h1 (graphToEFk k g1) == g2) && (apply h2 (graphToEFk k g2) == g1)

-- Given a duplicator strategy builds the graph morphism f: EFk(A) -> B
buildMorphFromStrat :: (Show (Vertex a), Show (Vertex b), Graph a, Graph b, GraphCoerce a, GraphCoerce b, Ord a, Ord (Vertex a), Ord (Vertex b),
                        Eq (Vertex a), Eq (Vertex b)) => (Int -> a -> b -> [Vertex a] -> [Vertex b])
                        -> Int -> a -> b -> GraphMorphism (EF a) b
buildMorphFromStrat strat k glin1 glin2 = GM (last Prelude.. strat k glin1 glin2)

