{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE TypeFamilies           #-} 
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE StandaloneDeriving     #-}

module Graphs where

import GHC.Exts (Constraint)
import Data.List

import Debug.Trace
import Category


class Graph g where
    type Vertex g
    edges :: g -> [(Vertex g,Vertex g)]
    graphFromEdgeList :: [(Vertex g,Vertex g)] -> g

gmap :: (Graph a, Graph b, Eq (Vertex b)) => (Vertex a -> Vertex b) -> a -> b
gmap f g = graphFromEdgeList $ (nub (map (\e -> (f (fst e), f (snd e))) (edges g)))



data GraphMorphism a b where GM :: (Graph a, Graph b) => (Vertex a -> Vertex b) -> GraphMorphism a b 

newtype MyGraph a = MyGraph {myedges :: [(a,a)]} deriving (Show, Eq)

instance Graph (MyGraph a) where
    type Vertex (MyGraph a) = a
    edges = myedges
    graphFromEdgeList g = MyGraph g


data EF a where EFdata :: Graph a => [([Vertex a],[Vertex a])] -> EF a

deriving instance (Graph a, Show (Vertex a)) => Show (EF a)

instance Graph a => Graph (EF a) where
    type Vertex (EF a) = [Vertex a]
    edges = \(EFdata x) -> x            -- Graph a => EF1 a -> [([Vertex a],[Vertex a])]
    graphFromEdgeList e = EFdata e      -- Graph a => [([Vertex a],[Vertex a])] -> EF1 a

instance Category GraphMorphism where
    type Object GraphMorphism g = Graph g
    id          = GM Prelude.id
    GM f . GM g = GM (f Prelude.. g)


instance CFunctor EF GraphMorphism GraphMorphism where
     funcMap (GM f) = GM (map f)

instance CComonad EF GraphMorphism where
    counit          = GM last -- the universe of EF is none empty lists so this is ok
    extend (GM f)   = GM $ map f Prelude.. (tail Prelude.. inits) 

data Product a b where Prod :: (Graph a, Graph b) => [((Vertex a, Vertex b),(Vertex a, Vertex b))] -> Product a b

instance (Graph a, Graph b) => Graph (Product a b) where
    type Vertex (Product a b) = (Vertex a, Vertex b)
    edges = \(Prod x) -> x            
    graphFromEdgeList e = Prod e

instance CBifunctor Product GraphMorphism GraphMorphism GraphMorphism where
  bifuncMap (GM gm1) (GM gm2) = GM (\(x,y) -> (gm1 x, gm2 y))

-- finish defen
product :: (Graph a, Graph b) => a -> b -> Product a b
product g1 g2 = Prod []


-- finish coproduct implementation
data Coproduct a b where Coprod :: (Graph a, Graph a) => [((Vertex a, Vertex b),(Vertex a, Vertex b))] -> Coproduct a b

instance (Graph a, Graph b) => Graph (Coproduct a b) where
    type Vertex (Coproduct a b) = (Vertex a, Vertex b)
    edges = \(Coprod x) -> x            
    graphFromEdgeList e = Coprod e

instance CBifunctor Coproduct GraphMorphism GraphMorphism GraphMorphism where
  bifuncMap (GM gm1) (GM gm2) = GM (\(x,y) -> (gm1 x, gm2 y))


------------------ Example with two equivilent graphs  -------------------- 

graph1 :: MyGraph Int
graph1 = MyGraph [(1,2),(2,3)]

graph2 :: MyGraph Char
graph2 = MyGraph [('a','b'),('b','c')]

-- universe of a graph
universe :: (Graph a, Eq (Vertex a)) => a -> [Vertex a]
universe = nub Prelude.. concatMap f Prelude.. edges
  where f (x,y) = [x,y]

--given a universe gives all possbile plays for a k length game
plays :: Int -> [a] -> [[a]]
plays 1 uni = map (\x -> [x]) uni
plays k uni = ps ++ [(x:p)|x<-uni,p<-ps]
    where ps = plays (k-1) uni

-- Given a graph map each vertex to every play that is appears in and generate edges accordingly
-- Usually gives a massive graph
graphToMaxEFk :: (Graph a, Eq (Vertex a)) => Int -> a -> EF a
graphToMaxEFk k g = EFdata $ concatMap (\(x,y)->[(f x p1,f y p2)|p1<-ps,p2<-ps,elem x p1,elem y p2]) (edges g)
    where ps       = plays k (universe g)
          f y (x:xs)
            | x==y      = x:xs
            | otherwise = x:(f y xs)

-- Given a graph map each vertex to every play that is appears in and generate edges accordingly
-- Usually gives a massive graph
graphToReasonableEFk :: (Graph a, Eq (Vertex a)) => Int -> a -> EF a
graphToReasonableEFk k g = EFdata $ concatMap (\(x,y)->take 5 [(f x p1,f y p2)|p1<-ps,p2<-ps,elem x p1,elem y p2]) (edges g)
    where ps       = plays k (universe g)
          f y (x:xs)
            | x==y      = x:xs
            | otherwise = x:(f y xs)

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
xToPlay :: Eq a => a -> [[a]] -> [a]
xToPlay x plays = reverse (g x (head (filter (elem x) plays)) []) 
    where g x [] _ = [x]
          g x (m:ms) ps
            | m==x      = x:ps
            | otherwise = g x ms (m:ps)

-- Generate all breakings up of the universe into lists of length k plus remainder
-- e.g. for universe [1,2,3,4,5,6,7], k=3 generates all possible lists of the form
-- [[1,2,3],[4,5,6],[7]] or [[7,4,3],[2,5,6],[1]] and so on. Then maps each node in
-- the graph to the prefix of the list it occurs in (xToPlay). This should always 
-- a valid coalgebra
genCoalgs :: (Graph a, Eq (Vertex a)) => Int -> a -> [EF a]
genCoalgs k g = map (\p -> gmap (\x -> xToPlay x p) g) plays
    where plays = map (t k) (permutations (universe g))
          
t :: Int -> [a] -> [[a]]
t k xs
  | k < (length xs) = (take k xs) : (t k (drop k xs))
  | otherwise       = [xs]





liftMappingToEFMorphism ::(Graph a, Graph b) => (Vertex a -> Vertex b) -> GraphMorphism (EF a) b
liftMappingToEFMorphism f = GM f Category.. counit

myhomomorph :: GraphMorphism (EF (MyGraph Int)) (MyGraph Char) 
myhomomorph = liftMappingToEFMorphism f 
  where f 1 = 'a'
        f 2 = 'b'
        f 3 = 'c'

apply :: (Graph a, Graph b, Eq (Vertex b)) => GraphMorphism a b -> a -> b
apply (GM gm) = gmap gm

--res1 = apply myhomomorph (head (liftGraphToEFkGraphs 1 graph1)) == graph2

------------------ Example with linear orderings  -------------------- 
-- Given a list representing a linear ordering it returns the equivilent
-- graph with the edge relation interpreted as the < relation
linToGraph :: [a] -> MyGraph a
linToGraph xs = MyGraph (f xs)
  where f [] = []
        f (x:xs) = map (\y -> (x,y)) xs ++ f xs

count :: Eq a => a -> [a] -> Int
count x = foldr (\y xs-> if x==y then xs + 1 else xs) 0

-- converts a graph to a linear order
-- Pre: Graph is a representation of a lin order
graphToLin :: (Graph a, Eq (Vertex a)) => a -> [Vertex a]
graphToLin g = reverse $ map fst $ sortBy (\(_,a) (_,b) -> compare a b) $ map (\x -> (x,count x e)) (universe g)
    where e = map fst (edges g)

-- Pre: elem x xs
split :: Eq a => a -> [a] -> ([a],[a])
split x xs = f [] xs
    where f xs (y:ys) = if x == y then (reverse (x:xs), x:ys) else f (y:xs) ys
          
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
strategy :: (Graph a, Graph b, Eq (Vertex a), Eq (Vertex b)) => Int -> a -> b -> [Vertex a] -> [Vertex b]
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
    | otherwise               = lin2 !! (2^(k-1))
    where (lin1LT,lin1GT) = split a lin1



buildMorphEFkAtoB :: (Graph a, Graph b, Eq (Vertex a), Eq (Vertex b)) => Int -> a -> b -> GraphMorphism (EF a) b
buildMorphEFkAtoB k glin1 glin2 = GM (last Prelude.. strategy k glin1 glin2)

checkEFkMorph :: (Graph a, Graph b, Eq (Vertex b), Eq (Vertex a)) => Int -> a -> b -> b
checkEFkMorph k glin1 glin2 = apply (buildMorphEFkAtoB k glin1 glin2) eflin1
    where eflin1 = head $ genCoalgs k glin1

lin1 = linToGraph [1..17]
lin2 = linToGraph [3..22]

lin3 = linToGraph [1,2,3]

lin4 = linToGraph [1..9]
lin5 = linToGraph [4..12]

lin6 = linToGraph [1..4]
lin7 = linToGraph [5..8]

------------------ Tree depth experiments  -------------------- 


getConnectedComponants :: a -> Graph a -> Graph b   