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

module Data.Graph.HGraph.Instances where

import Data.Functor.Identity
import Data.Proxy
import Data.Tagged

import Data.Graph.HGraph

type Never = Proxy
type Always = Identity

pattern Always a = Identity a
pattern Never = Proxy

-- | The underlying HGraph uses @Node@s.
-- This instance unwraps @Node@s and tries to find a way to point one node body at the other.
instance {-# OVERLAPPING #-} (a `DispatchOnTyCons` b) => Node i (e (j ': is)) a `PointsAt` Node j (f js) b where
  Node a `pointsAt` Node b = Node $ a `pointsAtDispatcher` b

-- | Using overlapping instances in @PointsAtInternal@ quickly turns into a hot mess.
-- Instead, we use a trick in which an outer type class with @Proxy@s controls
-- which instance of an inner type class applies.
-- In particular, @NoTyCon@, which witnesses that the type variable @a@
-- is not of the form @f b@ is very useful.
class DispatchOnTyCons a b where
  pointsAtDispatcher :: a -> b -> a
-- | Both the left and right side of `PointsAt` are of the form @f a@ (e.g. @Maybe Int@ and not @Int@).
instance
  {-# OVERLAPPING #-}
  ( lf ~ HandleLeft (TyConType f)
  , rf ~ TyConType g
  , PointsAtInternal lf rf (f a) (g b)
  ) =>
  DispatchOnTyCons (f a) (g b) where
  pointsAtDispatcher = pointsAtInternal (Proxy :: Proxy lf) (Proxy :: Proxy rf)
-- | Only the right side is of the form @f a@.
instance
  {-# OVERLAPPING #-}
  (rf ~ TyConType g, PointsAtInternal NoTyCon rf a (g b)) =>
  DispatchOnTyCons a (g b) where
  pointsAtDispatcher = pointsAtInternal (Proxy :: Proxy NoTyCon) (Proxy :: Proxy rf)
-- | Only the left side is of the form @f a@.
instance
  {-# OVERLAPPING #-}
  (lf ~ HandleLeft (TyConType f)
  , PointsAtInternal lf NoTyCon (f a) b
  ) =>
  DispatchOnTyCons (f a) b where
  pointsAtDispatcher = pointsAtInternal (Proxy :: Proxy lf) (Proxy :: Proxy NoTyCon)
-- | Neither side is higher kinded.
instance
  (PointsAtInternal NoTyCon NoTyCon a b) =>
  DispatchOnTyCons a b where
  pointsAtDispatcher = pointsAtInternal (Proxy :: Proxy NoTyCon) (Proxy :: Proxy NoTyCon)

data NoTyCon
data SomeFunctor
data Always'
data Never'
data Maybe'
data List

-- We need this family to be open so we can extend the @PointsAtInternal@
-- machinery to work with other type constructors like @Entity@.
type family TyConType (f :: * -> *) :: *
type instance TyConType Always = Always'
type instance TyConType Never = Never'
type instance TyConType Maybe = Maybe'
type instance TyConType [] = List

-- | Collapsing some of the functors on the left hand side of @PointsAt@ into @SomeFunctor@
-- saves us from defining some duplicative instances.
type family HandleLeft f
type instance HandleLeft Never' = Never'
type instance HandleLeft Always' = SomeFunctor
type instance HandleLeft Maybe' = SomeFunctor
type instance HandleLeft List = SomeFunctor


-- | Helpers that automatically provide certain additional @PointsAt@ instances
-- in terms of a few base @instances@.
class PointsAtInternal leftTyCon rightTyCon a b where
  pointsAtInternal :: Proxy leftTyCon -> Proxy rightTyCon -> a -> b -> a

-- | The base case. Once you reach this instance head, you must have a concretely declared instance.
-- e.g. @instance Student `PointsAt` Maybe (Entity Teacher)@
instance
  (a `PointsAt` Maybe b) =>
  PointsAtInternal NoTyCon Maybe' a (Maybe b) where
  pointsAtInternal Proxy Proxy a b = a `pointsAt` b
-- | The second base case.
instance
  (a `PointsAt` b) =>
  PointsAtInternal NoTyCon NoTyCon a b where
  pointsAtInternal Proxy Proxy a b = a `pointsAt` b

-- | If we can @pointAt@ a @Maybe@, we also know how to point at an @Always@.
instance
  (PointsAtInternal NoTyCon Maybe' a (Maybe b)) =>
  PointsAtInternal NoTyCon Always' a (Always b) where
  pointsAtInternal p Proxy a (Always b) = pointsAtInternal p (Proxy :: Proxy Maybe') a (Just b)

-- | If we know how to @pointAt@ a @Maybe@, we also know how to point at a @Never@.
instance
  (PointsAtInternal NoTyCon Maybe' a (Maybe b)) =>
  PointsAtInternal NoTyCon Never' a (Never b) where
  pointsAtInternal p Proxy a Never = pointsAtInternal p (Proxy :: Proxy Maybe') a (Nothing :: Maybe b)

-- | @Never@ can point at anything without incurring any constraints because it's a no-op.
instance
  PointsAtInternal Never' r (Never a) b where
  pointsAtInternal Proxy Proxy Never _ = Never

-- | Unless otherwise specified, functors @pointAt@ via @fmap@.
instance
  (Functor f, a `DispatchOnTyCons` b) =>
  PointsAtInternal SomeFunctor r (f a) b where
  pointsAtInternal Proxy Proxy fa b = (`pointsAtDispatcher` b) <$> fa
