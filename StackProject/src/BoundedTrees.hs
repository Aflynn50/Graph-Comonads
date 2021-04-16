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
{-# LANGUAGE KindSignatures #-}


{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}


module BoundedTrees where

import GHC.TypeLits
import GHC.TypeLits.Extra 
import GHC.Exts (Constraint)
import Data.List
import Data.Maybe
import Data.Coerce
import Data.Tree
import Data.Proxy



-- A test to see if the extra solver is enabled 

-- x :: Proxy (30 :: Nat)
-- x = Proxy
-- y :: Proxy (25 :: Nat)
-- y = Proxy
-- z :: Proxy (5 :: Nat)
-- z = f x y
-- f :: (KnownNat n, KnownNat m) => Proxy n -> Proxy m -> Proxy (GCD n m) 
-- f a b = Proxy

-- d = sameNat (Proxy :: Proxy 4) (Proxy :: Proxy (Max 4 2))

-- A tree of depth n or less
data SmallTree n a where
    SmallTree :: (KnownNat k, KnownNat n, k<=n) => KTree (Proxy k) a -> SmallTree (Proxy n) a

-- A tree of depth n
data KTree n a where
    KNode :: (KnownNat n) => {
        kRootLabel :: a,                 -- ^ label value
        kSubForest :: SubForests (Proxy (n-1)) a -- ^ zero or more child trees
    } -> KTree (Proxy n) a

-- A list of trees, n is the maximum of the depths of the trees
data SubForests n a where
    SFNil :: SubForests (Proxy (0::Nat)) a
    SFCons :: (KnownNat m, KnownNat n) => KTree (Proxy m) a -> SubForests (Proxy n) a -> SubForests (Proxy (Max n m)) a

-- -- map for Subforests - takes them to a list
-- sfmap :: (KnownNat n) => (forall (n::Nat). KTree (Proxy n) a -> b) -> (SubForests (Proxy n) a) -> [b] 
-- sfmap f SFNil           = []
-- sfmap f (SFCons kt kts) = f kt : sfmap f kts

-- -- sfmap (ktfoldr f) :: KTree (Proxy n) a -> b) -> (SubForests (Proxy n-1) a) -> [b]
-- ktfoldr :: (KnownNat n, KnownNat (n-1)) => (a -> [b] -> b) -> KTree (Proxy n) a -> b 
-- ktfoldr f (KNode l st) = f l (sfmap (ktfoldr f) st)

-- Specify n at the type level
-- Is this possible with a foldTree or do the types get in the way too much?
-- Also have I got the use of natVal right? I want to get the value from the type.
-- treeToSmallTree :: (1<=n, KnownNat n) => Tree a -> Maybe (SmallTree (Proxy n) a)
-- treeToSmallTree t = if depth < natVal Proxy then Just (SmallTree (ft t)) else Nothing
--     where depth  = foldTree (\_ xs -> if null xs then 0 else 1 + maximum xs) t
--           ft :: (KnownNat n1) => forall (n1::Nat). Tree a -> KTree (Proxy n1) a
--           ft (Node x xs) = KNode x (sft xs)
--           sft ::  (KnownNat n2) => forall (n2::Nat). [Tree a] -> SubForests (Proxy n2) a
--           sft []     = SFNil
--           sft (x:xs) = SFCons (ft x) (sft xs)

