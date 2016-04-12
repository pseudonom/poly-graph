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
import Database.Persist
import Database.Persist.Sql
import Debug.Trace
import Generics.Eot (Void, fromEot, toEot, Eot, HasEot)
import GHC.TypeLits
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

type family TypeError (msg :: Symbol) (a :: k) :: j

instance
  {-# OVERLAPPING #-}
  (Show (Key a)) =>
  Nullify (Maybe (Key a)) where
  nullify a = trace ("Nullify " ++ show a) Nothing
instance
  {-# OVERLAPPING #-}
  (Show (Key a), TypeError "Missing pointer to" a) =>
  Nullify (Key a) where
  nullify a = trace ("Preserve2 " ++ show a) a
instance
  {-# OVERLAPPABLE #-}
  (Show a) =>
  Nullify a where
  nullify a = trace ("Preserve " ++ show a) a

data Entity'

type instance TyConType Entity = Entity'
type instance HandleLeft Entity' = Entity'
instance Normalize (Entity a) where
  type NormalizedCon (Entity a) = Entity'
  type NormalizedT (Entity a) = Entity a
  normalize = id

_entityVal :: Lens' (Entity a) a
_entityVal pure' (Entity i e) = (\e' -> Entity i e') <$> pure' e

instance ToBase (Entity a) where
  type HasBase (Entity a) = 'True
  type Base (Entity a) = a
  base = _entityVal

instance (a `DispatchOnTyCons` b) => PointsAtInternal Entity' r (Entity a) b where
  pointsAtInternal Proxy Proxy (Entity i a) b = Entity i $ a `pointsAtDispatcher` b
instance (a `PointsAt` Entity b) => PointsAtInternal NoTyCon Entity' a (Entity b) where
  pointsAtInternal Proxy Proxy a b = a `pointsAt` b

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
    Node i is a -> ReaderT backend m ()

instance
  (BaseBackend backend ~ PersistEntityBackend a) =>
  InsertEntityElement (Entity a) backend where
  insertEntityElement (Node (Entity key val)) = insertKey key val
instance
  (BaseBackend backend ~ PersistEntityBackend a, Traversable f) =>
  InsertEntityElement (f (Entity a)) backend where
  insertEntityElement (Node fe) = traverse_ (\(Entity key val) -> insertKey key val) fe


type family Unwrap a where
  Unwrap (Entity a) = a
  Unwrap (f (Entity a)) = f a
type family UnwrapAll a where
  UnwrapAll ('(a, i, is) ': as) = '(Unwrap a, i, is) ': UnwrapAll as
  UnwrapAll '[] = '[]


class InsertGraph a b backend where -- | a -> b, b -> a, a -> backend , b -> backend where
  insertGraph ::
    (Monad m, MonadIO m, PersistStore backend, UnwrapAll b ~ a) =>
    HGraph a -> ReaderT backend m (HGraph b)

-- | HGraph base case (can't be the empty list because then we won't know which type of @backend@ to use)
instance
  (InsertElement a b is backend, Show a, HasEot a, GNullify (Eot a)) =>
  InsertGraph '[ '(a, i, is)] '[ '(b, i, is)] backend where
  insertGraph (a `Cons` Nil) = do
    e <- insertElement a
    pure $ e `Cons` Nil

-- | HGraph recursive case
instance
  ( (i `Member` (e ': f)) ~ 'UniqueName
  , Node i '( '[], is) a `PointsAtR` HGraph (e ': f)
  , InsertGraph (b ': c) (e ': f) backend
  , InsertElement a d is backend
  ) =>
  InsertGraph ('(a, i, is) ': b ': c) ('(d, i, is) ': e ': f) backend where
  insertGraph (a `Cons` b) = do
    b' <- insertGraph b
    let a' = a `pointsAtR` b'
    a'' <- insertElement a'
    pure $ a'' `Cons` b'


class InsertElement a b is backend | a -> b, b -> a, a -> backend, b -> backend where
  insertElement ::
    (Monad m, MonadIO m, PersistStore backend, Unwrap b ~ a) =>
    Node i '( '[], is) a -> ReaderT backend m (Node j js b)
instance
  (PersistEntityBackend a ~ BaseBackend backend, PersistEntity a, HasEot a, GNullify (Eot a)) =>
  InsertElement a (Entity a) '[] backend where
  insertElement (Node a) = Node . flip Entity a' <$> insert a'
    where a' = fromEot . gNullify . toEot $ a
instance
  (PersistEntityBackend a ~ BaseBackend backend, PersistEntity a) =>
  InsertElement a (Entity a) (i ': is) backend where
  insertElement (Node a) = Node . flip Entity a <$> insert a
instance
  (Show (f a), HasEot a, GNullify (Eot a), PersistEntityBackend a ~ BaseBackend backend, PersistEntity a, Traversable f, Applicative f) =>
  InsertElement (f a) (f (Entity a)) '[] backend where
  insertElement (Node fa) = do
    trace ("inserting " ++ show fa) (pure ())
    let fa' = fromEot . gNullify . toEot <$> fa
    fid <- traverse insert fa'
    pure $ Node (Entity <$> fid <*> fa')
instance
  (Show (f a), PersistEntityBackend a ~ BaseBackend backend, PersistEntity a, Traversable f, Applicative f) =>
  InsertElement (f a) (f (Entity a)) (i ': is) backend where
  insertElement (Node fa) = do
    trace ("inserting " ++ show fa) (pure ())
    fid <- traverse insert fa
    pure $ Node (Entity <$> fid <*> fa)


instance (ToBackendKey SqlBackend a) => Arbitrary (Key a) where
  arbitrary = toSqlKey <$> arbitrary
instance (PersistEntity a, Arbitrary (Key a), Arbitrary a) => Arbitrary (Entity a) where
  arbitrary = Entity <$> arbitrary <*> arbitrary
