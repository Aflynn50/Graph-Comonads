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
--{-# LANGUAGE DataKinds              #-}
--{-# LANGUAGE PolyKinds              #-}



module Lib
    ( someFunc
    ) where

import Data.List


-- Universe of graph given by the type - could parameterise by a list of vertacies instead.
newtype Graph a = Graph {edges :: [(a,a)]}
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
  (.) :: a -> Morphism a y z -> Morphism a x y -> Morphism a x z

instance ConcreteMetaCat GraphCat where
  type Object GraphCat = Graph
  type Morphism GraphCat = GraphMorphism

instance ConcreteCat GraphCat where
  id GraphCat = GraphMorphism Prelude.id 
  (.) GraphCat (GraphMorphism v2) (GraphMorphism v1) = GraphMorphism (v2 Prelude.. v1)

class Endofunctor cat f where
  funcMap :: cat -> Morphism cat a b -> Morphism cat (f a) (f b) 

class Endofunctor cat f => Comonad cat f where
  counit    :: cat -> Morphism cat (f a) a
  coextend  :: cat -> Morphism cat (f a) b -> Morphism cat (f a) (f b)  


-- kindof want EF to have kind * -> Graph [a]
newtype EF a = EF (Graph [a])
-- Would it be better to do Graph EF a and EF a :: [a] -> EF a
data EF1 a where EF1 :: [a] -> EF1 a


efmap    f (EF1 xs) = EF1 $ map f xs
eflast     (EF1 xs) = last xs
efextend f (EF1 xs) = EF1 $ map (\x -> f (EF1 x)) ((tail Prelude.. inits) xs) -- f:: EF2 a -> a

instance Endofunctor GraphCat EF1 where
    funcMap GraphCat gm = GraphMorphism $ efmap (unGM gm)

instance Comonad GraphCat EF1 where
    counit   GraphCat    = GraphMorphism eflast
    coextend GraphCat gm = GraphMorphism $ efextend (unGM gm)

newtype EF2 a = EF2 {funcAction :: Graph a -> Graph [a]}

-- efmap    f xs = map f xs
-- eflast     xs = last xs
-- efextend f xs = EF2 $ map f ((tail Prelude.. inits) xs) -- f:: EF2 a -> a

-- instance Endofunctor GraphCat EF2 where
--     funcMap GraphCat gm = GraphMorphism (efmap (unGM gm))

-- instance Comonad GraphCat EF2 where
--     counit   GraphCat    = GraphMorphism eflast
--     coextend GraphCat gm = GraphMorphism $ efextend (unGM gm)


data EF3 a where EF3 :: Graph [a] -> EF3 a

coerce :: EF3 a -> Graph [a]
coerce (EF3 x) = x

someFunc = "spag"
-- instance Endofunctor GraphCat EF3 where
--     funcMap GraphCat gm = GraphMorphism (map (unGM gm))

-- instance Comonad GraphCat EF3 where
--     counit   GraphCat    = GraphMorphism last
--     coextend GraphCat gm = GraphMorphism $ map (unGM gm) Prelude.. tail Prelude.. inits


--data EF3 :: forall a . Graph a -> Graph (EF1 a)


-- instance Endofunctor GraphCat EF where
--     funcMap GraphCat gm = GraphMorphism map (unGM gm)

-- instance Comonad GraphCat EF where
--     counit   GraphCat    = GraphMorphism last
--     coextend GraphCat gm = GraphMorphism $ map (tail Prelude.. inits) (unGM gm)

