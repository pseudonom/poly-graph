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
type instance HandleLeft Maybe = SomeFunctor
type instance HandleLeft [] = SomeFunctor

-- | Helpers that automatically provide certain additional @PointsAt@ instances
-- in terms of a few base @instances@.
class PointsAtInternal leftTyCon a b where
  pointsAtInternal :: Proxy leftTyCon -> a -> b -> a

instance
  (a `PointsAt` Maybe b) =>
  PointsAtInternal NoTyCon a (Maybe b) where
  pointsAtInternal Proxy a b = a `pointsAt` b

-- | Unless otherwise specified, functors @pointAt@ via @fmap@.
instance
  (Functor f, a `DispatchOnTyCons` b) =>
  PointsAtInternal SomeFunctor (f a) b where
  pointsAtInternal Proxy fa b = (`pointsAtDispatcher` b) <$> fa
