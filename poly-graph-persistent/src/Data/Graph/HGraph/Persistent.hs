{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- Pattern synonyms and exhaustivity checking don't work well together
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Graph.HGraph.Persistent where

import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.IO.Class (MonadIO)
import Data.Foldable (traverse_)
import Data.Functor.Identity
import Data.Proxy
import Data.Tagged
import Database.Persist

import Data.Graph.HGraph
import Data.Graph.HGraph.Internal

type Never = Proxy
type Always = Identity

pattern Always a = Identity a
pattern Never = Proxy

instance
  {-# OVERLAPPING #-}
  (b `GPointsAt` (Entity a)) =>
  (Key a, b) `GPointsAt` (Entity a) where
  (_, b) `gPointsAt` e@(Entity k _) = (k, b `gPointsAt` e)
instance
  {-# OVERLAPPING #-}
  (b `GPointsAt` (Maybe (Entity a))) =>
  (Maybe (Key a), b) `GPointsAt` (Maybe (Entity a)) where
  (_, b) `gPointsAt` e@(Just (Entity k _)) = (Just k, b `gPointsAt` e)
  (_, b) `gPointsAt` e@(Nothing) = (Nothing, b `gPointsAt` e)
instance
  {-# OVERLAPPING #-}
  (b `GPointsAt` (Entity a)) =>
  (Maybe (Key a), b) `GPointsAt` (Entity a) where
  (_, b) `gPointsAt` e@(Entity k _) = (Just k, b `gPointsAt` e)


class InsertEntityGraph a backend | a -> backend where
  insertEntityGraph ::
    (Monad m, MonadIO m, PersistStore backend) =>
    HGraph a -> ReaderT backend m ()

-- | HGraph base case (can't be the empty list because then we won't know which type of @backend@ to use)
instance
  (InsertEntityElement a backend) =>
  InsertEntityGraph '[ '(a, i, is)] backend where
  insertEntityGraph (a `Cons` Nil) = insertEntityElement a
-- | HGraph recursive case
instance
  (InsertEntityElement a backend, InsertEntityGraph (b ': c) backend) =>
  InsertEntityGraph ('(a, i, is) ': b ': c) backend where
  insertEntityGraph (a `Cons` b) = insertEntityGraph b >> insertEntityElement a


class InsertEntityElement a backend | a -> backend where
  insertEntityElement ::
    (Monad m, MonadIO m, PersistStore backend) =>
    Tagged t a -> ReaderT backend m ()

instance
  (BaseBackend backend ~ PersistEntityBackend a) =>
  InsertEntityElement (Entity a) backend where
  insertEntityElement (Tagged (Entity key val)) = insertKey key val
instance
  (BaseBackend backend ~ PersistEntityBackend a, Traversable f) =>
  InsertEntityElement (f (Entity a)) backend where
  insertEntityElement (Tagged fe) = traverse_ (\(Entity key val) -> insertKey key val) fe


type family Unwrap a where
  Unwrap (Entity a) = a
  Unwrap (f (Entity a)) = f a
type family UnwrapAll a where
  UnwrapAll ('(a, i, is) ': as) = '(Unwrap a, i, is) ': UnwrapAll as
  UnwrapAll '[] = '[]


class InsertGraph a b backend | a -> b, b -> a, a -> backend , b -> backend where
  insertGraph ::
    (Monad m, MonadIO m, PersistStore backend, UnwrapAll b ~ a) =>
    HGraph a -> ReaderT backend m (HGraph b)

-- | HGraph base case (can't be the empty list because then we won't know which type of @backend@ to use)
instance
  (InsertElement a b backend) =>
  InsertGraph '[ '(a, i, is)] '[ '(b, i, is)] backend where
  insertGraph (a `Cons` Nil) = do
    e <- insertElement a
    pure $ e `Cons` Nil
-- | HGraph recursive case
instance
  ( Tagged '(i, is) a `PointsAtR` HGraph (e ': f)
  , InsertGraph (b ': c) (e ': f) backend
  , InsertElement a d backend
  ) =>
  InsertGraph ('(a, i, is) ': b ': c) ('(d, i, is) ': e ': f) backend where
  insertGraph (a `Cons` b) = do
    b' <- insertGraph b
    let a' = a `pointsAtR` b'
    a'' <- insertElement a'
    pure $ a'' `Cons` b'


class InsertElement a b backend | a -> b, b -> a, a -> backend, b -> backend where
  insertElement ::
    (Monad m, MonadIO m, PersistStore backend, Unwrap b ~ a) =>
    Tagged t a -> ReaderT backend m (Tagged u b)
instance
  (PersistEntityBackend a ~ BaseBackend backend, PersistEntity a) =>
  InsertElement a (Entity a) backend where
  insertElement (Tagged a) = Tagged . flip Entity a <$> insert a
instance
  (PersistEntityBackend a ~ BaseBackend backend, PersistEntity a, Traversable f, Applicative f) =>
  InsertElement (f a) (f (Entity a)) backend where
  insertElement (Tagged fa) = do
    fid <- traverse insert fa
    pure $ Tagged (Entity <$> fid <*> fa)
