{-# LANGUAGE FlexibleInstances      #-} 
{-# LANGUAGE UndecidableInstances   #-} 
{-# LANGUAGE MultiParamTypeClasses  #-} 
{-# LANGUAGE TypeFamilies           #-} 
{-# LANGUAGE ConstraintKinds        #-} 
{-# LANGUAGE FlexibleContexts       #-} 
{-# LANGUAGE GADTs                  #-} 
{-# LANGUAGE ScopedTypeVariables    #-} 
{-# LANGUAGE RankNTypes             #-}
--{-# LANGUAGE DataKinds              #-}
--{-# LANGUAGE PolyKinds              #-}



module Lib
    ( someFunc
    ) where

import Data.List
--import File2 ()
import File3 ()


-- Universe of graph given by the type - could parameterise by a list of vertacies instead.
newtype Graph a = Graph {edges :: [(a,a)]} deriving (Show, Eq)
-- A morphism between graphs is given by a function on vetecies
newtype GraphMorphism a b = GraphMorphism {unGM :: a -> b}

data GraphCat = GraphCat

gmap :: (a->b) -> Graph a -> Graph b
gmap f g = Graph $ map (\e -> (f (fst e), f (snd e))) (edges g)

class ConcreteMetaCat a where
  type Object a :: * -> *
  type Morphism a :: * -> * -> *

class ConcreteMetaCat a => ConcreteCat a where
  id :: a -> Morphism a x x
  compose :: a -> Morphism a y z -> Morphism a x y -> Morphism a x z

instance ConcreteMetaCat GraphCat where
  type Object GraphCat = Graph
  type Morphism GraphCat = GraphMorphism

instance ConcreteCat GraphCat where
  id GraphCat = GraphMorphism Prelude.id 
  compose GraphCat (GraphMorphism v2) (GraphMorphism v1) = GraphMorphism (v2 Prelude.. v1)

class Endofunctor cat f where
  funcMap :: cat -> Morphism cat a b -> Morphism cat (f a) (f b) 

class Endofunctor cat f => Comonad cat f where
  counit    :: cat -> Morphism cat (f a) a
  coextend  :: cat -> Morphism cat (f a) b -> Morphism cat (f a) (f b)  


-- Since morphisms are no dependent on graphs this makes sense
data EF1 a where EF1 :: [a] -> EF1 a
-- To apply this functor to an object we need to apply it to the inner type of the object
-- i.e. Graph a -> Graph (EF a)

efmap    f (EF1 xs) = EF1 $ map f xs
eflast     (EF1 xs) = last xs
efextend f (EF1 xs) = EF1 $ map (\x -> f (EF1 x)) ((tail Prelude.. inits) xs) -- f:: EF2 a -> a

instance Endofunctor GraphCat EF1 where
    funcMap GraphCat gm = GraphMorphism $ efmap (unGM gm)

instance Comonad GraphCat EF1 where
    counit   GraphCat    = GraphMorphism eflast
    coextend GraphCat gm = GraphMorphism $ efextend (unGM gm)

graph1 :: Graph Int
graph1 = Graph [(1,2),(2,3)]

graph2 :: Graph Char
graph2 = Graph [('a','b'),('b','c')]

-- universe of a graph
universe :: Eq a => Graph a -> [a]
universe = nub . concatMap f . edges
  where f (x,y) = [x,y]

--possbile plays for a k length game
plays :: Int -> [a] -> [[a]]
plays 0 uni = [[]]
plays k uni = concat [map (x:) (plays (k-1) uni) | x <- uni]

-- given a play and a graph G maps each x in G to shortest play sequence with x in it
graphToEFk :: Eq a => [a] -> Graph a -> Graph (EF1 a)
graphToEFk play = gmap (\x -> EF1 $ takeWhile (/= x) play ++ [x]) 

-- Gives all the possible EF Graphs for a k length game
liftGraphToEFkGraphs :: Eq a => Int -> Graph a -> [Graph (EF1 a)]
liftGraphToEFkGraphs k g = map (`graphToEFk` g) (plays k (universe g))

liftMappingToEFMorphism :: (a -> b) -> GraphMorphism (EF1 a) b
liftMappingToEFMorphism f = compose GraphCat (GraphMorphism f) (counit GraphCat)

myhomomorph :: GraphMorphism (EF1 Int) Char 
myhomomorph = liftMappingToEFMorphism f 
  where f 1 = 'a'
        f 2 = 'b'
        f 3 = 'c'

apply :: GraphMorphism a b -> Graph a -> Graph b
apply gm = gmap (unGM gm)



someFunc = apply myhomomorph (head (liftGraphToEFkGraphs 1 graph1)) == graph2
