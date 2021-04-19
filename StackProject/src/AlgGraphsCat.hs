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


-- EF and Pebble comonad over graphs using algebraic adjaceny map graphs. 

-- The category of graphs is a category or relational structures over the signitue (edge :: Arity 2)
-- In this program graphs have an underlying vertex type, the elements of this type are taken to be the 
-- universe of the relational structure. This means that we consider graphs equal up to the set of edges,
-- i.e. we ignore vertices of degree 0. 

----------- The category of graphs -----------

-- Morphisms in the categroy of Graphs

-- Ideally these would be graph homomorphims, however, implementing type level graph homomorphisms in haskell
-- is not easy (or maybe not even possible). It would be easy enough to represent them as a pair of graphs and
-- a mapping between them the could easily be checked however in that case the two graphs would have to be known
-- when constructing the morphism.
-- Instead, I have chosen to represent them as vertex maps. A graph morphism can be used to generate the graph of 
-- codomain by applying the map to all vertices of the graph and preserving the edge structure. This is 
-- nececerraly a subset of graph homomorpisms. Graphs are respresented as adjacency maps from the Algebraic graphs 
-- library, these merge vertices with the same value, so the number of edges of the codomain graph is less than 
-- or equal to that of the domain graph.
-- This cannot, for example, represent that graph homomorpism between a unconnected and connected graph of a given
-- set of vertices 
data GraphMorphism a b where GM :: (Graph a, Graph b) => (Vertex a -> Vertex b) -> GraphMorphism a b 

instance Category GraphMorphism where
    type Object GraphMorphism g = Graph g
    id          = GM Prelude.id
    GM f . GM g = GM (f Prelude.. g)

-- Ideally the objects of the category would be any type that implements Graph, however the Algebraic
-- Graphs Graph class only gives functions for construction of graphs, not deconstruction. Because of
-- this it is useful to have a concrete datatype for graphs. Ideally this would not be needed however
-- without depenent types this becomes very difficult for reasons outlined in other comments. 
-- AdjacencyMaps have been chosen becuase they are an efficient representation that comes with a
-- useful set of algorithms for graph manipulation. 
-- GraphCoerce provides a way of transforming a graph that has been acted on by a functor back into
-- an adjacency map, thus allowing these functions to be used on it. 
class Graph g => GraphCoerce g where
    gcoerce    :: g -> AdjacencyMap (Vertex g)
    gcoerceRev :: AdjacencyMap (Vertex g) -> g

-- We need the Ord here because the Graph instance for AdjMaps needs it for a lot of useful commands
-- e.g. vertexList, edgeList...
instance Ord a => GraphCoerce (AdjacencyMap a) where
    gcoerce    = Prelude.id
    gcoerceRev = Prelude.id

-- The EF and Pebble comonads arnt really a functors, simply becuase we cant apply them to all members of  
-- the category, specifically graphs of type EF a, it can only be applied to an adjmap. It is possible to
-- apply it to an EF a by first using gcoerce but it would be a lot nicer if we could actually apply
-- the functor straight to anything that satisifed the Graph constraint. I've tried to make this work
-- but it would require some type level programming stuff that I don't understand yet. The crux of the
-- problem seems to be that when defining graph functions (overlay, connect...) for EF the actual type
-- of the graph that these would be applied to is unknow at compile time (since it is any graph that
-- implements GraphCoerce). Due to time constraints I have opted to leave this as it is.

-- Ideally EF would look something like this:
-- data EF a where EFdata :: (Graph a, Graph b, Vertex b ~ [Vertex a], GraphCoerce b) => b -> EF a

------ The Ehrenfeucht-Fraı̈ssé Comonad ------
-- Should technically be non empty lists rather than just haskell lists

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

-- We automatically get the definition of the EF functor from the defn in Category.hs

deriving instance (Graph a, Ord a, Show a, Ord (Vertex a), Show (Vertex a)) => Show (EF a)    

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

------ Useful functors ------

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


-- getCoequalizer :: (Graph c, Graph d, Vertex c ~ a, Vertex d ~ b, Ord a, Eq a, Eq b) =>    
--         AdjacencyMap a -> AdjacencyMap b -> GraphMorphism c d -> GraphMorphism c d -> (AdjacencyMap a, GraphMorphism c c)

------ Useful functions ------

-- Apply a graph homomorphism to a graph
apply :: (Graph a, Graph b, GraphCoerce a, GraphCoerce b, Ord (Vertex a), Ord (Vertex b)) => GraphMorphism a b -> a -> b
apply (GM gm) g = gcoerceRev (gmap gm (gcoerce g))


-- Check if each edge in g1 is mapped by gm to an edge in g2
checkMorphIsHomo :: (Graph a, Graph b, GraphCoerce a, GraphCoerce b, Eq (Vertex b)) => a -> b -> GraphMorphism a b -> Bool
checkMorphIsHomo g1 g2 (GM gm) = foldr (\e b -> elem e eG2 && b) True eMapped
    where eMapped = map (\(x,y) -> (gm x,gm y)) (edgeList (gcoerce g1))
          eG2     = edgeList (gcoerce g2)


-- Get all edges in g1 (and their mappings under gm) that are not mapped to an edge in g2 by gm
checkMorphIsHomoDebug :: (Graph a, Graph b, GraphCoerce a, GraphCoerce b, Eq (Vertex b))
                            => a -> b -> GraphMorphism a b -> [((Vertex a, Vertex a),(Vertex b, Vertex b))]
checkMorphIsHomoDebug g1 g2 (GM gm) = [(e1,e2)| (e1,e2) <- eMapped,not (elem e2 eG2)]
    where eMapped = map (\(x,y) -> ((x,y),(gm x,gm y))) (edgeList (gcoerce g1))
          eG2     = edgeList (gcoerce g2)

-- vertices of a graph
gvertices :: (GraphCoerce a, Eq (Vertex a)) => a -> [Vertex a]
gvertices = nub Prelude.. vertexList Prelude.. gcoerce

-- Given a list of values generate all possible plays of lenght k
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

-- Performs the action of the EFk functor
graphToEFk :: (GraphCoerce a, Eq (Vertex a), Ord (Vertex a)) => Int -> a -> EF a
graphToEFk k g = EFdata $ AdjMap.edges $
    concatMap (\p -> mapMaybe (\e -> f e p) edgesOfg) ps
    where edgesOfg  = edgeList (gcoerce g)
          ps        = plays k (gvertices g)
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

-- graphToEFk usually gives a massive graph so this gives a subgraph of it
graphToLimEFk :: (GraphCoerce a, Eq (Vertex a), Ord (Vertex a)) => Int -> Int -> a -> EF a
graphToLimEFk lim k g = EFdata $ AdjMap.edges $
    concat $ take lim $ map (\p -> map (\(x,y) -> (f p x, f p y)) edgesOfg) ps
    where edgesOfg = edgeList (gcoerce g)
          ps       = plays k (gvertices g)
          f (x:xs) y  -- get prefix of play ending in y
            | x==y      = [x]
            | otherwise = x:(f xs y)

-- Check if efg is a valid EF k graph built from g
checkValidEFkGraph :: (Eq (Vertex g1), GraphCoerce g1, GraphCoerce g2, Vertex g2 ~ [Vertex g1]) => Int -> g1 -> g2 -> Bool
checkValidEFkGraph k g efg = foldr f True (edgeList (gcoerce efg))
    where gedges      = edgeList (gcoerce g)
          f (xs,ys) b = length xs <= k && length ys <= k
                        && elem (last xs,last ys) gedges
                        && (isPrefixOf xs ys || isPrefixOf ys xs)
                        && b

-- Check if pebg is a valid Peb k graph built from g
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

-- Given a duplicator strategy builds the graph morphism f: EFk(A) -> B
buildMorphFromStrat :: (Show (Vertex a), Show (Vertex b), Graph a, Graph b, GraphCoerce a, GraphCoerce b, Ord a, Ord (Vertex a), Ord (Vertex b),
                        Eq (Vertex a), Eq (Vertex b)) => (Int -> a -> b -> [Vertex a] -> [Vertex b])
                        -> Int -> a -> b -> GraphMorphism (EF a) b
buildMorphFromStrat strat k glin1 glin2 = GM (last Prelude.. strat k glin1 glin2)


---------- Proof checkers ----------

-- Checks for equailty in the exisential positvie fragment with quantifier rank k (i.e. checks for isomorphism)
eqQRankKEPfrag :: (Eq a, Eq b, Ord a, Ord b, Ord (Vertex a), Ord (Vertex b), GraphCoerce a, GraphCoerce b) 
                    => Int -> CoKleisli EF GraphMorphism a b -> CoKleisli EF GraphMorphism b a -> a -> b -> Bool
eqQRankKEPfrag k (CoKleisli h1) (CoKleisli h2) g1 g2 = 
                    (AdjMap.isSubgraphOf (gcoerce (apply h1 (graphToEFk k g1))) (gcoerce g2)) &&
                    (AdjMap.isSubgraphOf (gcoerce (apply h2 (graphToEFk k g2))) (gcoerce g1))

-- Checks for equailty in the fragment quantifier rank k with counting quantifiers (i.e. checks for isomorphism)
eqQRankKCounting :: (Eq a, Eq b, Ord a, Ord b, Ord (Vertex a), Ord (Vertex b), GraphCoerce a, GraphCoerce b) 
                    => Int -> CoKleisli EF GraphMorphism a b -> CoKleisli EF GraphMorphism b a -> a -> b -> Bool
eqQRankKCounting k (CoKleisli h1) (CoKleisli h2) g1 g2 = 
                    (apply h1 (graphToEFk k g1) == g2) && (apply h2 (graphToEFk k g2) == g1)



