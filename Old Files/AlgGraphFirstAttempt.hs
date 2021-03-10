{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE FlexibleInstances      #-} 
{-# LANGUAGE UndecidableInstances   #-} 
{-# LANGUAGE MultiParamTypeClasses  #-} 
{-# LANGUAGE FunctionalDependencies #-} 
{-# LANGUAGE TypeFamilies           #-} 
{-# LANGUAGE ConstraintKinds        #-} 
{-# LANGUAGE FlexibleContexts       #-} 
{-# LANGUAGE TupleSections          #-} 
{-# LANGUAGE GADTs                  #-} 
{-# LANGUAGE ScopedTypeVariables    #-} 
{-# LANGUAGE PackageImports         #-}
{-# LANGUAGE RankNTypes             #-}


module Lib
    ( someFunc
    ) where

import Prelude ()

import Control.Category.Constrained.Prelude
import qualified Control.Category.Hask as Hask

import Control.Monad.Constrained ()

import Algebra.Graph.Class

data GraphHomomorphism a b where 
    GH :: (a->b) -> GraphHomomorphism a b


gid :: Graph a => a -> a
gid g = g

instance Category GraphHomomorphism where
    type Object GraphHomomorphism g = Graph g
    id = GH gid
    (GH h1) . (GH h2) = GH (h1 . h2)

--applyGH :: GraphHomomorphism a b -> Graph a -> Graph b
--applyGH (GH f) g = 

--Homomorphism conditions 

data Basic a = Empty
             | Vertex a
             | Overlay (Basic a) (Basic a)
             | Connect (Basic a) (Basic a)
             deriving Show

instance Graph (Basic a) where
    type Vertex (Basic a) = a
    empty   = Empty
    vertex  = Vertex
    overlay = Overlay
    connect = Connect

instance (Ord a, Num a) => Num (Basic a) where
    fromInteger = vertex . fromInteger
    (+)         = overlay
    (*)         = connect
    signum      = const empty
    abs         = id
    negate      = id


newtype GraphFunctor a = 
    F {gfor :: forall g. Graph g => (a->Vertex g) -> g }

instance Graph (GraphFunctor a) where
    type Vertex (GraphFunctor a) = a
    empty       = F $ \_ -> empty -- is this empty on the argument graph?
    vertex x    = F $ \f -> vertex (f x)
    overlay x y = F $ \f -> overlay (gmap f x) (gmap f y)
    connect x y = F $ \f -> connect (gmap f x) (gmap f y)

gmap :: Graph g => (a->Vertex g) -> GraphFunctor a -> g
gmap = flip gfor 
-- becuase gfor is GraphFunctor a -> (a -> Vertex g) -> g
-- its implicitly defined that way with record syntax

f :: Int -> Vertex (Basic Int)
f x = x

gf :: GraphFunctor Int 
gf = vertex 1


-- class Graph g where
--  type Vertex g
--  empty :: g
--  vertex :: Vertex g -> g
--  overlay :: g -> g -> g
--  connect :: g -> g -> g

-- gmap :: (Graph a, Graph b) => (Vertex a-> Vertex b) -> Graph b -> Graph a

outputgraph = gmap f gf

instance Graph (Basic a) where
    type Vertex (Basic a) = a
    empty   = Empty
    vertex  = Vertex
    overlay = Overlay
    connect = Connect

instance (Ord a, Num a) => Num (Basic a) where
    fromInteger = vertex . fromInteger
    (+)         = overlay
    (*)         = connect
    signum      = const empty
    abs         = id
    negate      = id

myFirstGraph :: Basic Int
myFirstGraph = (vertex 1 + vertex 2) * (vertex 3 + vertex 4)

basicmap :: (a->b) -> Basic a -> Basic b
basicmap f (Vertex x) = Vertex (f x)
basicmap f (Overlay x y) = Overlay (basicmap f x) (basicmap f y)
basicmap f (Connect x y) = Connect (basicmap f x) (basicmap f y) 


x :: GraphFunctor Int 
x = F {}

gmap (vertex . (+1)) myFirstGraph

someFunc :: IO ()
someFunc = putStrLn "someFunc"
