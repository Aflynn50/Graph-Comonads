{-# LANGUAGE FlexibleInstances      #-} 
{-# LANGUAGE UndecidableInstances   #-} 
{-# LANGUAGE MultiParamTypeClasses  #-} 
{-# LANGUAGE TypeFamilies           #-} 
{-# LANGUAGE ConstraintKinds        #-} 
{-# LANGUAGE FlexibleContexts       #-} 
{-# LANGUAGE GADTs                  #-} 
{-# LANGUAGE ScopedTypeVariables    #-} 
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE FunctionalDependencies #-} 
--{-# LANGUAGE ExistentialQuantification #-} 

module File2
    ( res
    ) where

import Prelude ()
import Control.Category.Constrained.Prelude
import qualified Control.Category.Hask as Hask

-- Universe of graph given by the Vertex g
-- Could maybe instead use functional dependencies and do Graph g a | g -> a
class Graph g where
    type Vertex g
    edges :: g -> [(Vertex g,Vertex g)]
    graphFromEdgeList :: [(Vertex g,Vertex g)] -> g

gmap :: (Graph a, Graph b) => (Vertex a -> Vertex b) -> a -> b
gmap f g = graphFromEdgeList $ map (\e -> (f (fst e), f (snd e))) (edges g)

-- A morphism between graphs is given by a function on vetecies
data GraphMorphism a b where GraphMorphism :: (a -> b) -> GraphMorphism a b

instance Category GraphMorphism where
    type Object GraphMorphism g = Graph g
    id  = GraphMorphism id
    GraphMorphism f . GraphMorphism g = GraphMorphism (f . g)

newtype MyGraph a = MyGraph {myedges :: [(a,a)]} deriving (Show, Eq)

instance Graph (MyGraph a) where
    type Vertex (MyGraph a) = a
    edges = myedges
    graphFromEdgeList g = MyGraph g

data EF a where EF :: [a] -> EF a

-- instance Functor EF GraphMorphism GraphMorphism  where
--     fmap (GraphMorphism f) = GraphMorphism g
--             where g (EF xs) = EF (map f xs) 



res = ()
