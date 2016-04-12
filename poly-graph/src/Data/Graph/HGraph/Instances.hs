{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
-- Pattern synonyms and exhaustivity checking don't work well together
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Graph.HGraph.Instances where

import Data.Proxy

import Data.Graph.HGraph

-- | The underlying HGraph uses @Node@s.
-- This instance unwraps @Node@s and tries to find a way to point one node body at the other.
instance {-# OVERLAPPING #-} (a `DispatchOnTyCons` b) => Node i (j ': is) a `PointsAt` Node j js b where
  Node a `pointsAt` Node b = Node $ a `pointsAtDispatcher` b

-- | Using overlapping instances in @PointsAtInternal@ quickly turns into a hot mess.
-- Instead, we use a trick in which an outer type class with @Proxy@s controls
-- which instance of an inner type class applies.
-- In particular, @NoTyCon@, which witnesses that the type variable @a@
-- is not of the form @f b@ is very useful.
class DispatchOnTyCons a b where
  pointsAtDispatcher :: a -> b -> a
-- | The left side is of the form @f a@.
instance
  {-# OVERLAPPING #-}
  (lf ~ HandleLeft f
  , PointsAtInternal lf (f a) b
  ) =>
  DispatchOnTyCons (f a) b where
  pointsAtDispatcher = pointsAtInternal (Proxy :: Proxy lf)
-- | The left hand side isn't higher kinded.
instance
  (PointsAtInternal NoTyCon a b) =>
  DispatchOnTyCons a b where
  pointsAtDispatcher = pointsAtInternal (Proxy :: Proxy NoTyCon)

data NoTyCon
data SomeFunctor
data Never'

-- | Collapsing some of the functors on the left hand side of @PointsAt@ into @SomeFunctor@
-- saves us from defining some duplicative instances.
type family HandleLeft (f :: * -> *) :: *
type instance HandleLeft Never = Never'
type instance HandleLeft Always = SomeFunctor
type instance HandleLeft Maybe = SomeFunctor
type instance HandleLeft [] = SomeFunctor

-- | Helpers that automatically provide certain additional @PointsAt@ instances
-- in terms of a few base @instances@.
class PointsAtInternal leftTyCon a b where
  pointsAtInternal :: Proxy leftTyCon -> a -> b -> a

instance {-# OVERLAPPABLE #-}
  (PointsAtInternal NoTyCon a (NormalizedT (c b)), Normalize (c b)) =>
  PointsAtInternal NoTyCon a (c b) where
  pointsAtInternal p a c = pointsAtInternal p a (normalize c)

-- | @Never@ can point at anything without incurring any constraints because it's a no-op.
instance
  PointsAtInternal Never' (Never a) b where
  pointsAtInternal Proxy Never _ = Never

-- | Unless otherwise specified, functors @pointAt@ via @fmap@.
instance
  (Functor f, a `DispatchOnTyCons` b) =>
  PointsAtInternal SomeFunctor (f a) b where
  pointsAtInternal Proxy fa b = (`pointsAtDispatcher` b) <$> fa

-- | This class provides a generalized framework for handling multiple similar types.
-- That is, instead of having to write a separate @PointsAtInternal@ instance for each combination of types,
-- we can just specify a base case and how to reduce the other types to that base case.
class Normalize a where
  type NormalizedT a
  normalize :: a ->  NormalizedT a

-- | A normalization group. @Always@ and @Never@ can be reduced to @Maybe@.
instance Normalize (Always a) where
  type NormalizedT (Always a) = Maybe a
  normalize (Always a) = Just a
instance Normalize (Never (a :: *)) where
  type NormalizedT (Never a) = Maybe a
  normalize Never = Nothing
-- | If you define @NormalizedT a = a@, you must also define a @PointsAtInternal@ instance to handle it.
-- If you don't, you'll just end up spinning as @pointsAtInternal@ calls itself.
instance Normalize (Maybe a) where
  type NormalizedT (Maybe a) = Maybe a
  normalize = id
instance
  (a `PointsAt` Maybe b) =>
  PointsAtInternal NoTyCon a (Maybe b) where
  pointsAtInternal Proxy a b = a `pointsAt` b
