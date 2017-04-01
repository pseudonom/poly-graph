{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- Pattern synonyms and exhaustivity checking don't work well together
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Graph.HGraph.Persistent where

import Control.Arrow ((&&&))
import Control.Lens (partsOf, (^..), (%%~))
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Foldable (traverse_, toList)
import qualified Data.List as List
import Data.List.NonEmpty (NonEmpty, nonEmpty)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Proxy
import Data.Text (unpack)
import Database.Persist
import Generics.Eot (Eot, HasEot)
import GHC.TypeLits hiding (TypeError)
import Test.QuickCheck (vector)
import Test.QuickCheck.Arbitrary (Arbitrary(..))
import Test.QuickCheck.Gen (generate, Gen)

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

instance (Base a ~ a) => ToBase (Entity a) where
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

-- | HGraph base case (can't be the empty list because then we won't know which type of @backend@ to use)
instance
  ( InsertElement a b backend baseBackend, HasEot a, GNullify a ps (Eot a)
  , PointsAtR i is a '[]
  , BaseBackend backend ~ baseBackend
  , PersistStoreWrite backend
  ) =>
  InsertGraph ps '[ '(i, is, a)] '[ '(i, is, b)] backend baseBackend where
  insertGraph' Proxy (rawNode `Cons` Nil) = do
    let Node updated = rawNode `pointsAtR` Nil
    inserted <- insertElement updated
    pure $ Node inserted `Cons` Nil

-- | HGraph recursive case
instance
  ( (i `Member` (e ': f)) ~ 'UniqueName
  , PointsAtR i is a (e ': f)
  , InsertGraph ps (b ': c) (e ': f) backend baseBackend
  , InsertElement a d backend baseBackend
  ) =>
  InsertGraph ps ('(i, is, a) ': b ': c) ('(i, is, d) ': e ': f) backend baseBackend where
  insertGraph' Proxy (rawNode `Cons` rawGraph) = do
    graph <- insertGraph' (Proxy :: Proxy ps) rawGraph
    let Node updated = rawNode `pointsAtR` graph
    inserted <- insertElement updated
    pure $ Node inserted `Cons` graph

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

-- Handy helper function for ensuring that a graph is unique in some attribute (e.g. email address)
unique :: (Eq c, SetAllOfType a b, GetAllOfType a b, Arbitrary c) => Lens' b c -> HGraph a -> Gen (HGraph a)
unique field graph = do
  if anySame (graph ^.. allOfType . field)
  then do
    -- Weirdly, switching this to `(=<<)` stops it from type checking
    graph' <- graph & partsOf (allOfType . field) %%~ vector . length
    unique field graph'
  else pure graph
  where
    anySame xs = length (List.nub xs) /= length xs

type family Wrap (a :: *) :: * where
  Wrap (f a) = f (Entity a)
  Wrap a = Entity a

type family WrapAll (as :: [(k, [k], *)]) :: [(k, [k], *)] where
  WrapAll ('(i, is, a) ': as) = '(i, is, Wrap a) ': WrapAll as
  WrapAll '[] = '[]

ensureGraphUniqueness
  :: (EnsureGraphUniqueness '[] a (WrapAll a))
  => HGraph a
  -> Gen (HGraph a)
ensureGraphUniqueness = ensureGraphUniqueness' (Proxy :: Proxy ('[] :: [*]))

class
  EnsureGraphUniqueness (ps :: [*]) (a :: [(k, [k], *)]) (b :: [(k, [k], *)]) | a -> b, b -> a where
  ensureGraphUniqueness' :: (WrapAll a ~ b) => Proxy ps -> HGraph a -> Gen (HGraph a)

instance EnsureGraphUniqueness ps '[] '[] where
  ensureGraphUniqueness' Proxy Nil = pure Nil

instance
  ( (i `Member` as) ~ 'UniqueName
  , EnsureGraphUniqueness ps as bs
  , EnsureUniqueness a b as
  ) =>
  EnsureGraphUniqueness ps ('(i, is, a) ': as) ('(i, is, b) ': bs) where
  ensureGraphUniqueness' Proxy (Node item `Cons` graph) = do
    uniquedGraph <- ensureGraphUniqueness' (Proxy :: Proxy ps) graph
    uniqueItem <- ensureUniqueness item uniquedGraph
    pure $ Node uniqueItem `Cons` uniquedGraph

-- | Update a to be unique in HGraph as
class EnsureUniqueness a b as | a -> b, b -> a where
  ensureUniqueness :: (Wrap a ~ b) => a -> HGraph as -> Gen a

-- | Check uniqueness for a by its Uniques modulo FKs
instance
  ( PersistEntity a
  , GetAllOfType as a
  , Arbitrary a
  , Eq (Unique a)
  ) => EnsureUniqueness a (Entity a) as where
  ensureUniqueness a graph = do
    let others = getAllOfType graph
    if any (duplicateUniqueFields a) others
      then do
        new <- arbitrary
        ensureUniqueness new graph
      else pure a

-- | Check uniqueness by looking inside Functor-shaped values and ensuring
-- that the values in the Functor itself are unique together
instance
  ( Wrap a ~ Entity a
  , Traversable f
  , EnsureUniqueness a (Entity a) as
  , IsInternallyConsistent (f a) (f (Entity a))
  , Arbitrary a
  ) => EnsureUniqueness (f a) (f (Entity a)) as where
  ensureUniqueness fa graph = do
    fa' <- traverse (`ensureUniqueness` graph) fa
    if isInternallyConsistent fa'
      then pure fa'
      else do
        fa'' <- traverse (const arbitrary) fa' -- This could be less drastic
        ensureUniqueness fa'' graph

-- | Check that a context-free value is internally consistent
class IsInternallyConsistent a b | a -> b, b -> a where
  isInternallyConsistent :: a -> Bool

-- | Collections of entities should not have duplicates
instance
  ( Foldable f
  , PersistEntity a
  , Eq (Unique a)
  ) => IsInternallyConsistent (f a) (f (Entity a)) where
  isInternallyConsistent fa =
    length (List.nubBy duplicateUniqueFields items) == length items
   where
    items = toList fa

-- | Check that two records have the same unique fields ignoring
-- FKs since they'll probably be manipulated later by the graph machinery
duplicateUniqueFields :: (Eq (Unique r), PersistEntity r) => r -> r -> Bool
duplicateUniqueFields x y =
  fromMaybe False $ do
    xs <- comparableUniques Nothing xUniques
    ys <- comparableUniques Nothing yUniques
    return $ xs == ys
 where
  xUniques = persistUniqueKeys x
  yUniques = persistUniqueKeys (y `copyUniqueFksFrom` xUniques)

comparableUniques :: PersistEntity r => Maybe r -> [Unique r] -> Maybe (NonEmpty (Unique r))
comparableUniques mr =
  nonEmpty . filter (not . onlyHasFks)
 where
  nameToRef = Map.fromList ((fieldHaskell &&& fieldReference) <$> entityFields (entityDef mr))
  onlyHasFks = all (isForeignRef . (nameToRef Map.!) . fst) . persistUniqueToFieldNames
  isForeignRef ForeignRef{} = True
  isForeignRef _ = False

-- | Copy FKs used in a Unique constraint from the list of Uniques
-- into the record. This keeps us from considering arbitrary FKs
-- that will later be overwritten as contributing to uniqueness.
copyUniqueFksFrom :: PersistEntity r => r -> [Unique r] -> r
r `copyUniqueFksFrom` xs =
  right $ fromPersistValues $ do
    ((key, refType), original) <- zip keys values
    case refType of
      ForeignRef{} -> pure (fromMaybe original $ Map.lookup key updates)
      _ -> pure original
 where
  keys = (fieldHaskell &&& fieldReference) <$> entityFields (entityDef $ Just r)
  values = toPersistValue <$> toPersistFields r
  updates = generateUpdates xs
  right (Left t) = error $ "copyUniqueFksFrom: " ++ unpack t
  right (Right s) = s

-- | Generate a Map of updates from Uniques
generateUpdates :: PersistEntity r => [Unique r] -> Map HaskellName PersistValue
generateUpdates =
  Map.fromList . concatMap toPairs
 where
  toPairs x = zip (fst <$> persistUniqueToFieldNames x) (persistUniqueToValues x)
