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
-- TODO: Remove this once we're using the official TypeError
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

module Data.Graph.HGraph.Persistent where

import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.IO.Class (MonadIO)
import Data.Foldable (traverse_)
import Data.Proxy
import Database.Persist
import Database.Persist.Sql
import Generics.Eot (Eot, HasEot)
import GHC.TypeLits hiding (TypeError)
import Test.QuickCheck.Arbitrary (Arbitrary(..))

import Data.Graph.HGraph
import Data.Graph.HGraph.Instances
import Data.Graph.HGraph.Internal

instance
  Key a `FieldPointsAt` Entity a where
  _ `fieldPointsAt` (Entity k _) = k
instance
  Maybe (Key a) `FieldPointsAt` Maybe (Entity a) where
  _ `fieldPointsAt` Just (Entity k _) = Just k
  _ `fieldPointsAt` Nothing = Nothing
instance
  Maybe (Key a) `FieldPointsAt` Entity a where
  _ `fieldPointsAt` (Entity k _) = Just k
instance
  {-# OVERLAPPABLE #-}
  a `FieldPointsAt` b where
  fieldPointsAt = const

type instance Base (Key a) = a

type family TypeError (b :: k) (msg :: Symbol) (a :: k) :: j

instance
  {-# OVERLAPPING #-}
  Nullify pointedFrom (Maybe (Key a)) where
  nullify Proxy = const Nothing
instance
  {-# OVERLAPPING #-}
  (TypeError pointedFrom " is missing pointer to " a) =>
  Nullify pointedFrom (Key a) where
  nullify Proxy = id
instance
  {-# OVERLAPPABLE #-}
  Nullify pointedFrom pointedTo where
  nullify Proxy = id

data Entity'

type instance HandleLeft Entity = Entity'
instance Normalize (Entity a) where
  type NormalizedT (Entity a) = Entity a
  normalize = id

_entityVal :: Lens' (Entity a) a
_entityVal pure' (Entity i e) = (\e' -> Entity i e') <$> pure' e

type instance Base (Entity a) = a
instance ToBase (Entity a) where
  base = _entityVal

instance (a `DispatchOnTyCons` b) => PointsAtInternal Entity' (Entity a) b where
  pointsAtInternal Proxy (Entity i a) b = Entity i $ a `pointsAtDispatcher` b
instance (a `PointsAt` Entity b) => PointsAtInternal NoTyCon a (Entity b) where
  pointsAtInternal Proxy a b = a `pointsAt` b

class InsertEntityGraph a backend | a -> backend where
  insertEntityGraph ::
    (MonadIO m, PersistStore backend) =>
    HGraph a -> ReaderT backend m ()

-- | HGraph base case (can't be the empty list because then we won't know which type of @backend@ to use)
instance
  (InsertEntityElement a backend) =>
  InsertEntityGraph '[ '(i, is, a)] backend where
  insertEntityGraph (Node a `Cons` Nil) = insertEntityElement a
-- | HGraph recursive case
instance
  (InsertEntityElement a backend, InsertEntityGraph (b ': c) backend) =>
  InsertEntityGraph ('(i, is, a) ': b ': c) backend where
  insertEntityGraph (Node a `Cons` b) = insertEntityGraph b >> insertEntityElement a


class InsertEntityElement a backend | a -> backend where
  insertEntityElement ::
    (MonadIO m, PersistStore backend) =>
    a -> ReaderT backend m ()

instance
  (BaseBackend backend ~ PersistEntityBackend a) =>
  InsertEntityElement (Entity a) backend where
  insertEntityElement (Entity key val) = insertKey key val
instance
  (BaseBackend backend ~ PersistEntityBackend a, Traversable f) =>
  InsertEntityElement (f (Entity a)) backend where
  insertEntityElement = traverse_ (\(Entity key val) -> insertKey key val)


type family Unwrap (a :: *) :: * where
  Unwrap (Entity a) = a
  Unwrap (f (Entity a)) = f a
type family UnwrapAll (as :: [(k, [k], *)]) :: [(k, [k], *)] where
  UnwrapAll ('(i, is, a) ': as) = '(i, is, Unwrap a) ': UnwrapAll as
  UnwrapAll '[] = '[]

insertGraph ::
  (MonadIO m, InsertGraph '[] (UnwrapAll b) b backend, PersistStoreWrite backend) =>
  HGraph (UnwrapAll b) -> ReaderT backend m (HGraph b)
insertGraph = insertGraph' (Proxy :: Proxy ('[] :: [*]))

class InsertGraph (ps :: [*]) (a :: [(k, [k], *)]) (b :: [(k, [k], *)]) (backend :: *) | a -> b, b -> a, a -> backend , b -> backend where
  insertGraph' ::
    (MonadIO m, PersistStore backend, UnwrapAll b ~ a) =>
    Proxy ps ->
    HGraph a -> ReaderT backend m (HGraph b)

-- -- | HGraph base case (can't be the empty list because then we won't know which type of @backend@ to use)
instance
  ( InsertElement a b backend, HasEot a, GNullify a ps (Eot a)
  , PointsAtR i is a '[]
  ) =>
  InsertGraph ps '[ '(i, is, a)] '[ '(i, is, b)] backend where
  insertGraph' Proxy (a `Cons` Nil) = do
    e <- insertElement . unNode  $ a `pointsAtR` Nil
    pure $ Node e `Cons` Nil

-- | HGraph recursive case
instance
  ( (i `Member` (e ': f)) ~ 'UniqueName
  , PointsAtR i is a (e ': f)
  , InsertGraph ps (b ': c) (e ': f) backend
  , InsertElement a d backend
  ) =>
  InsertGraph ps ('(i, is, a) ': b ': c) ('(i, is, d) ': e ': f) backend where
  insertGraph' Proxy (a `Cons` b) = do
    b' <- insertGraph' (Proxy :: Proxy ps) b
    let Node a' = a `pointsAtR` b'
    a'' <- insertElement a'
    pure $ Node a'' `Cons` b'


class InsertElement (a :: *) (b :: *) (backend :: *) | a -> b, b -> a, a -> backend, b -> backend where
  insertElement ::
    (MonadIO m, PersistStore backend, Unwrap b ~ a) =>
    a -> ReaderT backend m b
instance
  (PersistEntityBackend a ~ BaseBackend backend, PersistEntity a) =>
  InsertElement a (Entity a) backend where
  insertElement a = flip Entity a <$> insert a
instance
  (PersistEntityBackend a ~ BaseBackend backend, PersistEntity a, Traversable f, Applicative f) =>
  InsertElement (f a) (f (Entity a)) backend where
  insertElement fa = do
    fid <- traverse insert fa
    pure $ Entity <$> fid <*> fa


instance (ToBackendKey SqlBackend a) => Arbitrary (Key a) where
  arbitrary = toSqlKey <$> arbitrary
instance (PersistEntity a, Arbitrary (Key a), Arbitrary a) => Arbitrary (Entity a) where
  arbitrary = Entity <$> arbitrary <*> arbitrary
