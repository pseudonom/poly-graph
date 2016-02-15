{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- Pattern synonyms and exhuastivity checking don't work well together
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module Data.Graph.HGraph.Persistent where

import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.IO.Class (MonadIO)
import Database.Persist

import Data.Graph.HGraph
import Data.Graph.HGraph.Arbitrary
import Data.Graph.HGraph.Internal

class InsertEntityGraph a where
  type InsertEntityGraphBackend a
  insertEntityGraph
    :: (Monad m, MonadIO m, PersistStore (InsertEntityGraphBackend a))
    => a -> ReaderT (InsertEntityGraphBackend a) m ()
instance
  ( InsertEntityGraph a, InsertEntityGraph b
  , InsertEntityGraphBackend a ~ InsertEntityGraphBackend b
  ) => InsertEntityGraph (a :~>: b) where
  type InsertEntityGraphBackend (a :~>: b) = InsertEntityGraphBackend a
  insertEntityGraph (a :~>: b) = insertEntityGraph b >> insertEntityGraph a
instance
  ( InsertEntityGraph a, InsertEntityGraph b
  , InsertEntityGraphBackend a ~ InsertEntityGraphBackend b
  ) => InsertEntityGraph (a, b) where
  type InsertEntityGraphBackend (a, b) = InsertEntityGraphBackend a
  insertEntityGraph (a, b) = insertEntityGraph a >> insertEntityGraph b
instance
  ( InsertEntityGraph a, InsertEntityGraph b, InsertEntityGraph c
  , InsertEntityGraphBackend a ~ InsertEntityGraphBackend b, InsertEntityGraphBackend b ~ InsertEntityGraphBackend c
  ) => InsertEntityGraph (a, b, c) where
  type InsertEntityGraphBackend (a, b, c) = InsertEntityGraphBackend a
  insertEntityGraph (a, b, c) = insertEntityGraph a >> insertEntityGraph b >> insertEntityGraph c
instance InsertEntityGraph (Never a) where
  type InsertEntityGraphBackend (Never a) = InsertEntityGraphBackend a
  insertEntityGraph Never = return ()
instance (InsertEntityGraph a) => InsertEntityGraph (Always a) where
  type InsertEntityGraphBackend (Always a) = InsertEntityGraphBackend a
  insertEntityGraph (Always a) = insertEntityGraph a
instance (InsertEntityGraph a) => InsertEntityGraph (Maybe a) where
  type InsertEntityGraphBackend (Maybe a) = InsertEntityGraphBackend a
  insertEntityGraph (Just a) = insertEntityGraph a
  insertEntityGraph Nothing = return ()
instance InsertEntityGraph (Entity a) where
  type InsertEntityGraphBackend (Entity a) = PersistEntityBackend a
  insertEntityGraph (Entity key val) = insertKey key val


class InsertGraph a where
  insertGraph
    :: (Monad m, MonadIO m, PersistStore (InsertGraphBackend a))
    => Unwrapped a -> ReaderT (InsertGraphBackend a) m a
  type Unwrapped a
  type InsertGraphBackend a
instance {-# OVERLAPPABLE #-}
  ( PersistEntityBackend a ~ backend, PersistEntity a
  ) => InsertGraph (Entity a) where
  type Unwrapped (Entity a) = a
  type InsertGraphBackend (Entity a) = PersistEntityBackend a
  insertGraph a = flip Entity a <$> insert a
instance
  ( a ~~> Entity b
  , InsertGraph (Entity a), InsertGraph (Entity b)
  , PersistEntity a, PersistEntity b
  , PersistEntityBackend a ~ backend, PersistEntityBackend b ~ backend
  ) => InsertGraph (Entity a :~>: Entity b) where
  type Unwrapped (Entity a :~>: Entity b) = a :~>: b
  type InsertGraphBackend (Entity a :~>: Entity b) = PersistEntityBackend a
  insertGraph (a :~>: b) = do
    b' <- insertGraph b
    a' <- insertGraph $ a ~~> b'
    -- We just did the linking in the previous line
    -- so we don't need to use `~>`
    -- and it imposes an extra `Entity a ~~> Entity b` constraint
    pure $ a' `PointsTo` b'
