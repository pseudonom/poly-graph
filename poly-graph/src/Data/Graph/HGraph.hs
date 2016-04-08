{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- Pattern synonyms and exhaustivity checking don't work well together
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module Data.Graph.HGraph
  ( module Data.Graph.HGraph
  , X.HGraph(Nil)
  , X._head
  , X._tail
  , X.Node(..)
  , X.retag
  ) where

import Data.Proxy
import Generics.Eot (Void, fromEot, toEot, Eot, HasEot)
import GHC.TypeLits
import Test.QuickCheck.Arbitrary

import Data.Graph.HGraph.Internal as X

infixr 5 `PointsAt`
class a `PointsAt` b where
  infixr 5 `pointsAt`
  pointsAt :: a -> b -> a
  default pointsAt :: (HasEot a, Eot a `GPointsAt` b) => a -> b -> a
  pointsAt a b = fromEot $ toEot a `gPointsAt` b

class a `GPointsAt` b where
  infixr 5 `gPointsAt`
  gPointsAt :: a -> b -> a
instance
  (a `GPointsAt` c, b `GPointsAt` c) =>
  Either a b `GPointsAt` c where
  Left a `gPointsAt` b = Left $ a `gPointsAt` b
  Right a `gPointsAt` b = Right $ a `gPointsAt` b
instance
  (a `FieldPointsAt` c, b `GPointsAt` c) =>
  (a, b) `GPointsAt` c where
  (a, b) `gPointsAt` c = (a `fieldPointsAt` c, b `gPointsAt` c)
instance GPointsAt () a where
  gPointsAt _ _ = ()
instance GPointsAt Void a where
  gPointsAt _ _ = error "impossible"

class FieldPointsAt a b where
  fieldPointsAt :: a -> b -> a

-- | "Read-only" pattern allows convenient destructuring while encouraging preservation
-- linkage invariant
infixr 5 :<
pattern a :< b <- Node a `Cons` b

class Nullify a where
  nullify :: a -> a

class GNullify a where
  gNullify :: a -> a
instance (GNullify a, GNullify b) => GNullify (Either a b) where
  gNullify (Left a) = Left $ gNullify a
  gNullify (Right b) = Right $ gNullify b
instance (Nullify a, GNullify b) => GNullify (a, b) where
  gNullify (a, b) = (nullify a, gNullify b)
instance GNullify () where
  gNullify _ = ()
instance GNullify Void where
  gNullify _ = error "impossible"

class a `PointsAtR` b where
  pointsAtR :: a -> b -> a

--- - | End of graph. Final node never pointed at anything. Default `Maybe`s to `Nothing`.
instance {-# OVERLAPPING #-} (HasEot a, GNullify (Eot a)) => Node i ('Right '[]) a `PointsAtR` HGraph '[] where
  -- We use `GNullify` so we can default a `Maybe` key at the end of the graph to `Nothing`
  Node a `pointsAtR` _ = Node . fromEot . gNullify $ toEot a
-- | End of graph. Final node used to point at things. Preserve the preceding nullification
instance {-# OVERLAPPING #-} Node i ('Left '[]) a `PointsAtR` HGraph '[] where
  pointsAtR = const
-- | Points at nothing. Never pointed at anything. Default `Maybe`s to `Nothing`.
instance (HasEot a, GNullify (Eot a)) => Node i ('Right '[]) a `PointsAtR` (HGraph b) where
  Node a `pointsAtR` _ = Node . fromEot . gNullify $ toEot a
-- | Points at nothing. Used to point at something. Preserve prior linking.
instance Node i ('Left '[]) a `PointsAtR` (HGraph b) where
  pointsAtR = const
-- | Points at wrong thing
instance (Node i (e (j ': js)) a `PointsAtR` HGraph c) => Node i (e (j ': js)) a `PointsAtR` (HGraph ('(b, k, ls) ': c)) where
  a `pointsAtR` Cons _ c = a `pointsAtR` c
-- | Adjacent
instance {-# OVERLAPPING #-}
  ( Node i (e (j ': js)) a `PointsAt` Node j ('Right ks) b
  , Node i ('Left js) a `PointsAtR` (HGraph ('(b, j, ks) ': c))
  ) =>
  Node i (e (j ': js)) a `PointsAtR` (HGraph ('(b, j, ks) ': c)) where
  a `pointsAtR` r@(Cons b _) = retag $ a' `pointsAtR` r
    where
      a' :: Node i ('Left js) a
      a' = retag $ a `pointsAt` b

infixr 5 ~>
(~>) ::
  ((i `Member` b) ~ 'UniqueName, Node i ('Right is) a `PointsAtR` HGraph b) =>
  a -> HGraph b -> HGraph ('(a, i, is) ': b)
a ~> b = (Node a `pointsAtR` b) `Cons` b

-- @RawGraph@ is required because, without it, we have to provide no-op @PointsAt@ instances for
-- building the @Arbitrary@ graph we hand to @insertGraph@. i.e.
-- @instance (a `PointsAt` Entity b) => a `PointsAt` b where a `pointsAt` _ = a@
-- But then any graphs missing an instance match this instance and fail via a context reduction stack overflow
-- which is pretty ugly.
data RawGraph a = RawGraph { unRawGraph :: HGraph a }

instance Arbitrary (RawGraph '[]) where
  arbitrary = pure $ RawGraph Nil
instance
  ((i `Member` b) ~ 'UniqueName, Arbitrary (Node i ('Right is) a), Arbitrary (RawGraph b)) =>
  Arbitrary (RawGraph ('(a, i, is) ': b)) where
  arbitrary = do
    RawGraph <$> (Cons <$> arbitrary <*> (unRawGraph <$> arbitrary))

instance Arbitrary (HGraph '[]) where
  arbitrary = pure Nil
instance
  ( (i `Member` b) ~ 'UniqueName, Node i ('Right is) a `PointsAtR` HGraph b
  , Arbitrary (Node i ('Right is) a), Arbitrary (HGraph b)
  ) =>
  Arbitrary (HGraph ('(a, i, is) ': b)) where
  arbitrary = do
    b <- arbitrary
    a <- arbitrary
    pure $ (a `pointsAtR` b) `Cons` b

class Pluck name a b | name a -> b where
  pluck :: Proxy name -> Lens' (HGraph a) b
instance {-# OVERLAPPING #-} Pluck name ('(b, name, is) ': c) b where
  pluck Proxy = _head
instance (Pluck name d b) => Pluck name ('(c, otherName, is) ': d) b where
  pluck p = _tail . pluck p

type Line as = HGraph (Line' as)

type family Line' (as :: [k]) :: [(k, k, [k])] where
  Line' '[k] = '[Ty k '[]]
  Line' (k ': l ': m) = Ty k '[l] ': Line' (l ': m)

type Ty a b = '(a, a, b)
