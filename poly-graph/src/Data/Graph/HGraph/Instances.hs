{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module Data.Graph.HGraph.Instances where

import Data.Functor.Identity
import Data.Proxy
import Data.Tagged
import Test.QuickCheck.Arbitrary (Arbitrary(..))

import Data.Graph.HGraph

type Never = Proxy
type Always = Identity

pattern Always a = Identity a
pattern Never = Proxy

instance (a `PointsAt` Maybe b) => a `PointsAt` Always b where
  a `pointsAt` Always b = a `pointsAt` (Just b :: Maybe b)
instance (a `PointsAt` Maybe b) => a `PointsAt` Never b where
  a `pointsAt` Never = a `pointsAt` (Nothing :: Maybe b)

instance {-# OVERLAPPABLE #-} (Functor f, a `PointsAt` b) => f a `PointsAt` b where
  fa `pointsAt` b = (`pointsAt` b) <$> fa

-- The above don't compose nicely because none is 'more specific' than the other.
-- So we write the combinations out by hand to increase specificity
instance {-# OVERLAPPING #-} (Functor f, a `PointsAt` Maybe b) => f a `PointsAt` Always b where
  fa `pointsAt` Always b = (`pointsAt` (Just b :: Maybe b)) <$> fa
instance {-# OVERLAPPING #-} (Functor f, a `PointsAt` Maybe b) => f a `PointsAt` Never b where
  fa `pointsAt` Never = (`pointsAt` (Nothing :: (Maybe b))) <$> fa
instance {-# OVERLAPPING #-} (Functor f, a `PointsAt` Maybe b) => f a `PointsAt` Maybe b where
  fa `pointsAt` b = (`pointsAt` b) <$> fa

instance {-# OVERLAPPABLE #-} (a `PointsAt` b) => a `PointsAt` Maybe b where
  a `pointsAt` Just b = a `pointsAt` b
  a `pointsAt` Nothing = a

-- The underlying HGraph uses @Node@s. This instance translates @Node@s into something slightly friendlier.
instance {-# OVERLAPPING #-} (a `PointsAt` b) => Node i (j ': is) a `PointsAt` Node j js b where
  Node a `pointsAt` Node b = Node $ a `pointsAt` b

instance (Arbitrary a) => Arbitrary (Node i is a) where
  arbitrary = Node <$> arbitrary
instance (Arbitrary a) => Arbitrary (Always a) where
  arbitrary = pure <$> arbitrary
instance Arbitrary (Never a) where
  arbitrary = pure Never
