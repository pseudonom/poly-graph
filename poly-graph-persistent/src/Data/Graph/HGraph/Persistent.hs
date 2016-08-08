{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- Pattern synonyms and exhaustivity checking don't work well together
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module Data.Graph.HGraph.Persistent where

import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Foldable (traverse_)
import Data.Proxy
import Database.Persist
import Generics.Eot (Eot, HasEot)
import GHC.TypeLits hiding (TypeError)
import Test.QuickCheck.Gen (generate)
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

type instance HandleLeft Entity = "Entity"

_entityVal :: Lens' (Entity a) a
_entityVal pure' (Entity i e) = (\e' -> Entity i e') <$> pure' e

type instance Base (Entity a) = a
instance ToBase (Entity a) where
  base = _entityVal

instance (a `DispatchOnTyCons` b) => PointsAtInternal "Entity" (Entity a) b where
  pointsAtInternal Proxy (Entity i a) b = Entity i $ a `pointsAtDispatcher` b
instance (a `PointsAt` Entity b) => PointsAtInternal "NoTyCon" a (Entity b) where
  pointsAtInternal Proxy a b = a `pointsAt` b

class InsertEntityGraph a backend baseBackend | a -> baseBackend where
  insertEntityGraph ::
    (MonadIO m, PersistStoreWrite backend) =>
    HGraph a -> ReaderT backend m ()

-- | HGraph base case (can't be the empty list because then we won't know which type of @backend@ to use)
instance
  (InsertEntityElement a backend baseBackend, BaseBackend backend ~ baseBackend) =>
  InsertEntityGraph '[ '(i, is, a)] backend baseBackend where
  insertEntityGraph (Node a `Cons` Nil) = insertEntityElement a
-- | HGraph recursive case
instance
  (InsertEntityElement a backend baseBackend, InsertEntityGraph (b ': c) backend baseBackend, BaseBackend backend ~ baseBackend) =>
  InsertEntityGraph ('(i, is, a) ': b ': c) backend baseBackend where
  insertEntityGraph (Node a `Cons` b) = insertEntityGraph b >> insertEntityElement a


class InsertEntityElement a backend baseBackend | a -> baseBackend where
  insertEntityElement ::
    (MonadIO m) =>
    a -> ReaderT backend m ()

instance
  (PersistEntityBackend a ~ baseBackend, BaseBackend backend ~ baseBackend, PersistStoreWrite backend) =>
  InsertEntityElement (Entity a) backend baseBackend where
  insertEntityElement (Entity key val) = insertKey key val
instance
  (Traversable f, PersistEntityBackend a ~ baseBackend, BaseBackend backend ~ baseBackend, PersistStoreWrite backend) =>
  InsertEntityElement (f (Entity a)) backend baseBackend where
  insertEntityElement = traverse_ (\(Entity key val) -> insertKey key val)


type family Unwrap (a :: *) :: * where
  Unwrap (Entity a) = a
  Unwrap (f (Entity a)) = f a
type family UnwrapAll (as :: [(k, [k], *)]) :: [(k, [k], *)] where
  UnwrapAll ('(i, is, a) ': as) = '(i, is, Unwrap a) ': UnwrapAll as
  UnwrapAll '[] = '[]

insertGraph ::
  (MonadIO m, InsertGraph '[] (UnwrapAll b) b backend baseBackend, BaseBackend backend ~ baseBackend) =>
  HGraph (UnwrapAll b) -> ReaderT backend m (HGraph b)
insertGraph = insertGraph' (Proxy :: Proxy ('[] :: [*]))

class
  (BaseBackend backend ~ baseBackend, PersistStoreWrite backend) =>
  InsertGraph (ps :: [*]) (a :: [(k, [k], *)]) (b :: [(k, [k], *)]) (backend :: *) (baseBackend :: *)
  | a -> b, b -> a, a -> baseBackend , b -> baseBackend where
  insertGraph' ::
    (MonadIO m, UnwrapAll b ~ a) =>
    Proxy ps -> HGraph a -> ReaderT backend m (HGraph b)

-- -- | HGraph base case (can't be the empty list because then we won't know which type of @backend@ to use)
instance
  ( InsertElement a b backend baseBackend, HasEot a, GNullify a ps (Eot a)
  , PointsAtR i is a '[]
  , BaseBackend backend ~ baseBackend
  , PersistStoreWrite backend
  ) =>
  InsertGraph ps '[ '(i, is, a)] '[ '(i, is, b)] backend baseBackend where
  insertGraph' Proxy (a `Cons` Nil) = do
    e <- insertElement . unNode  $ a `pointsAtR` Nil
    pure $ Node e `Cons` Nil

-- | HGraph recursive case
instance
  ( (i `Member` (e ': f)) ~ 'UniqueName
  , PointsAtR i is a (e ': f)
  , InsertGraph ps (b ': c) (e ': f) backend baseBackend
  , InsertElement a d backend baseBackend
  ) =>
  InsertGraph ps ('(i, is, a) ': b ': c) ('(i, is, d) ': e ': f) backend baseBackend where
  insertGraph' Proxy (a `Cons` b) = do
    b' <- insertGraph' (Proxy :: Proxy ps) b
    let Node a' = a `pointsAtR` b'
    a'' <- insertElement a'
    pure $ Node a'' `Cons` b'


class
  InsertElement (a :: *) (b :: *) (backend :: *) (baseBackend :: *) | a -> b, b -> a, a -> baseBackend, b -> baseBackend where
  insertElement ::
    (MonadIO m, Unwrap b ~ a) =>
    a -> ReaderT backend m b
instance
  (PersistEntity a, PersistEntityBackend a ~ baseBackend, BaseBackend backend ~ baseBackend, PersistStoreWrite backend) =>
  InsertElement a (Entity a) backend baseBackend where
  insertElement a = flip Entity a <$> insert a
instance
  (PersistEntity a, Traversable f, Applicative f, PersistEntityBackend a ~ baseBackend, BaseBackend backend ~ baseBackend, PersistStoreWrite backend) =>
  InsertElement (f a) (f (Entity a)) backend baseBackend where
  insertElement fa = do
    fid <- traverse insert fa
    pure $ Entity <$> fid <*> fa

insertGraphFromFragments
  :: (MonadIO m, Arbitrary (RawGraph z), z ~ UnwrapAll y, InsertGraph '[] z y backend baseBackend, PersistStoreWrite backend, BaseBackend backend ~ baseBackend)
  => Proxy y -> (HGraph z -> HGraph z) -> ReaderT backend m (HGraph z, HGraph y)
insertGraphFromFragments Proxy f = do
  graph <- liftIO (f . unRawGraph <$> generate arbitrary)
  (graph,) <$> insertGraph graph
