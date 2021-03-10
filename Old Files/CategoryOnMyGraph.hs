{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies    #-} 
{-# LANGUAGE PolyKinds       #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies       #-}


module File3
    ( res1
    ) where

import GHC.Exts (Constraint)
import Data.List


class Category (k :: κ -> κ -> *) where
  type Object k (o :: κ) :: Constraint
  type Object k o = ()
  id :: Object k a => k a a
  (.) :: (Object k a, Object k b, Object k c) 
         => k b c -> k a b -> k a c

class (Category r, Category t)
           => RFunctor f r t | f r -> t, f t -> r where
  fmap :: (Object r a, Object t (f a), Object r b, Object t (f b))
     => r a b -> t (f a) (f b)


class (RFunctor m k k) => RComonad m k where
    counit :: Object k a => k (m a) a
    coextend :: (Object k a, Object k b) => k (m a) b -> k (m a) (m b)


-- class Category cat => RFunctor cat f where
--     rfmap :: (Object f a, Object f b) => (a->b) -> f a -> f b 

-- class RFunctor f => RComonad f where
--     counit :: (Object f x) => f x -> x
--     coextend :: (Object f x, Object f y) => (f x -> y) -> f x -> f y 

-- class Endofunctor catMorph f where
--   funcMap :: catMorph -> catMorph a b -> catMorph (f a) (f b) 

-- class Endofunctor catMorph f => Comonad catMorph f where
--   ecounit    :: cat -> catMorph (f a) a
--   ecoextend  :: cat -> catMorph (f a) b -> catMorph (f a) (f b)

class Graph g where
    type Vertex g
    edges :: g -> [(Vertex g,Vertex g)]
    graphFromEdgeList :: [(Vertex g,Vertex g)] -> g

gmap :: (Graph a, Graph b) => (Vertex a -> Vertex b) -> a -> b
gmap f g = graphFromEdgeList $ map (\e -> (f (fst e), f (snd e))) (edges g)



data GraphMorphism a b where GraphMorphism :: (a -> b) -> GraphMorphism a b

newtype MyGraph a = MyGraph {myedges :: [(a,a)]} deriving (Show, Eq)

instance Graph (MyGraph a) where
    type Vertex (MyGraph a) = a
    edges = myedges
    graphFromEdgeList g = MyGraph g

instance Category GraphMorphism where
    type Object GraphMorphism g = Graph g
    id  = GraphMorphism Prelude.id
    GraphMorphism f . GraphMorphism g = GraphMorphism (f Prelude.. g)

data EF a where EF :: [a] -> EF a

instance RFunctor EF GraphMorphism GraphMorphism where
    fmap (GraphMorphism f) = GraphMorphism g
            where g (EF xs) = EF (map f xs) 

efmap    f (EF xs) = EF $ map f xs
eflast     (EF xs) = last xs
efextend f (EF xs) = EF $ map (\x -> f (EF x)) ((tail Prelude.. inits) xs) -- f:: EF2 a -> a

instance RComonad EF GraphMorphism where
    counit                     = GraphMorphism eflast
    coextend (GraphMorphism f) = GraphMorphism $ efextend f


res1 = ()