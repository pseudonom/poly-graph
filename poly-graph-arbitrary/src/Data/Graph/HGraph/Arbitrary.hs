{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- Pattern synonyms and exhaustivity checking don't work well together
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Make @Arbitrary@ polymorphic graphs
module Data.Graph.HGraph.Arbitrary where

import Data.Functor.Identity
import Data.Proxy
import Data.Tagged
import Test.QuickCheck.Arbitrary

import Data.Graph.HGraph

type Never = Proxy
type Always = Identity

pattern Always a = Identity a
pattern Never = Proxy

instance (Arbitrary a) => Arbitrary (Always a) where
  arbitrary = Always <$> arbitrary
instance Arbitrary (Never a) where
  arbitrary = pure Never
instance {-# OVERLAPPABLE #-} (a `PointsAt` b) => (Always a) `PointsAt` b where
  (Always a) `pointsAt` b = Always $ a `pointsAt` b
instance (a `PointsAt` Maybe b) => a `PointsAt` (Never b) where
  a `pointsAt` Never = a `pointsAt` (Nothing :: Maybe b)
instance (a `PointsAt` Maybe b) => a `PointsAt` (Always b) where
  a `pointsAt` (Always b) = a `pointsAt` Just b
instance {-# OVERLAPPING #-} (a `PointsAt` Maybe b) => (Always a) `PointsAt` (Maybe b) where
  (Always a) `pointsAt` b = Always $ a `pointsAt` b
instance {-# OVERLAPPING #-} (a `PointsAt` Maybe b) => (Always a) `PointsAt` (Always b) where
  Always a `pointsAt` Always b = Always $ a `pointsAt` Just b
instance {-# OVERLAPPING #-} (a `PointsAt` Maybe b) => (Always a) `PointsAt` (Never b) where
  (Always a) `pointsAt` Never = Always $ a `pointsAt` (Nothing :: Maybe b)

instance Arbitrary (HGraph '[]) where
  arbitrary = pure Nil
instance
  (Tagged '(i, is) a `PointsAtR` HGraph b, Arbitrary a, Arbitrary (HGraph b)) =>
  Arbitrary (HGraph ('(a, i, is) ': b)) where
  arbitrary = (~>) <$> arbitrary <*> arbitrary
