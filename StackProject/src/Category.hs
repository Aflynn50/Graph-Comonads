{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Category where

import Data.Kind
import Data.Coerce
import Data.Functor.Identity
import Prelude hiding ((.))

class Category (cat :: k -> k -> *) where
  type Object cat (o :: k) :: Constraint
  id :: (Object cat o) => cat o o
  (.) :: (Object cat a, Object cat b, Object cat c) => cat b c -> cat a b -> cat a c

class (Category dom, Category cod) => CFunctor f dom cod where
  funcMap :: (Object dom a, Object cod (f a), Object dom b, Object cod (f b)) => dom a b -> cod (f a) (f b)

class (Category dom1, Category dom2, Category cod)
  => CBifunctor f dom1 dom2 cod where
  bifuncMap :: (Object dom1 a, Object dom1 b,
   Object dom2 c, Object dom2 d,
   Object cod (f a c), Object cod (f b d))
   => dom1 a b -> dom2 c d -> cod (f a c) (f b d)

class (Category cat) => CComonad f cat where
  counit :: (Object cat a
    , Object cat (f a))
    => cat (f a) a
  extend :: (Object cat a
    , Object cat b
    , Object cat (f a)
    , Object cat (f b)) 
    => cat (f a) b
    -> cat (f a) (f b)
  duplicate :: (Object cat a
    , Object cat (f a)
    , Object cat (f (f a))) 
    => cat (f a) (f (f a))
  duplicate = extend Category.id


class (Category dom, Category cod, CFunctor l dom cod, CFunctor r cod dom) => Adjunction cod dom l r where
  eta :: (Object dom a, Object dom (l (r b))) => dom a b

-- Every comonad is automatically a functor
instance (Category cat, CComonad f cat) => CFunctor f cat cat where
  funcMap f = extend (f . counit)

data CoKleisli f cat a b where 
  CoKleisli :: (Category cat, CComonad f cat) => cat (f a) b -> CoKleisli f cat a b

instance Category (CoKleisli f cat) where
  type Object (CoKleisli f cat) a = (Category cat, CComonad f cat, Object cat a, Object cat (f a))
  id = CoKleisli counit
  (CoKleisli f) . (CoKleisli g) = CoKleisli (f . extend g)

-- I dont think giving the eilenberg moore category is possible in Haskell (with this cate defn), the 
-- objects would have to be functions, not sure how I could enforece this with a constraint. 
-- ConstraintKinds gives constraints kinds rather than leting kinds be constraints :(