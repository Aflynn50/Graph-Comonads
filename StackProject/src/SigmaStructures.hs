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
{-# LANGUAGE AllowAmbiguousTypes #-} 

module SigmaStructures where

import GHC.TypeLits
import Data.Set (Set(..))
import Data.Foldable
import Data.Kind
import Data.Functor.Identity

import Category 

type family NoId f a where
  NoId Identity a = a
  NoId f a = f a

-- Every (sig)nature has (sym)bols with an associated natural number called (Arity)
class Signature sig where 
  type Arity (sym :: sig) :: Nat

-- Typical representation of a fixed-length list using GHC.TypeLits' Nat
data Vector (n :: Nat) a where
  VZ :: Vector 0 a 
  VCons :: a -> Vector n a -> Vector (n+1) a

-- Need to derive a Ord instance for 'Vector n a' to create a Set of vectors. 
-- We can do this by using [a]'s Ord instance and folding 'Vector n a' into '[a]'
-- Thatis, turn the vector into a list and compare the lists
-- A Foldable instance gives the toList function
instance Foldable (Vector n) where
  foldMap f VZ = mempty
  foldMap f (VCons x l) = f x <> (foldMap f l)
instance Eq a => Eq (Vector n a) where
  vec1 == vec2 = (toList vec1) == (toList vec2) 
instance Ord a => Ord (Vector n a) where
  compare vec1 vec2 = compare (toList vec1) (toList vec2)

-- Lifted from finite-typelits package: 
-- https://hackage.haskell.org/package/finite-typelits-0.1.4.2/docs/src/Data.Finite.Internal.html#Finite
-- to use properly the functions in this package should be used 
newtype Finite (n :: Nat) = Finite Integer
  deriving (Eq, Ord)

-- This typeclass abstracts the binding of signature to a domain
-- This allows us to define interpretations for the symbols in the signature
-- Via data derived from the domain
-- f is a Functor
class Signature sig => SigStruct (sym :: sig) f dom where
  -- Data constructor for interpreting a (sym)bol in (sig)nature
  data Interpretation sym f dom :: *

  -- These are necessary properties that must be satisfied, by a function in Hask, in order for an Interpretation to be considered valid. Not sure if they are sufficent. 
  -- Membership relation on the set of values in the position determined by the second argument
  project :: (
      n ~ Arity (sym :: sig)
    , KnownNat n
    , Ord dom)
    => NoId f dom
    -> Finite n 
    -> Interpretation sym f dom
    -> Bool

  -- Membership relation on the underlying set of the interpretation
  isMember :: (
      n ~ Arity (sym :: sig) 
    , KnownNat n
    , Ord dom)
    => Vector n (NoId f dom) 
    -> Interpretation sym f dom
    -> Bool

-- data SigMorphism sig a b where 
--   SM :: (Signature sig, SigStruct sig f a, SigStruct sig f b)
--    => (a -> b) -> SigMorphism sig a b

-- instance Category SigCategory morph where
--   type Object (SigMorphism sig) s = SigStruct sig
--   id      = 

class Signature sig => SigCategory sig (morph :: * -> * -> *) where
  type SigStructs sig (o :: *) :: Constraint