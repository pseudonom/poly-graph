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
instance (a `GPointsAt` c, b `GPointsAt` c) => Either a b `GPointsAt` c where
  Left a `gPointsAt` b = Left $ a `gPointsAt` b
  Right a `gPointsAt` b = Right $ a `gPointsAt` b
instance GPointsAt () a where
  gPointsAt _ _ = ()
instance GPointsAt Void a where
  gPointsAt _ _ = error "impossible"

-- "Read-only" pattern allows convenient destructuring while encouraging preservation
-- linkage invariant
infixr 5 :<:
pattern a :<: b <- Node a `Cons` b

class GNullify a where
  gNullify :: a -> a
instance (GNullify a, GNullify b) => GNullify (Either a b) where
  gNullify (Left a) = Left $ gNullify a
  gNullify (Right b) = Right $ gNullify b
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
(~>) :: (Node i ('Right is) a `PointsAtR` HGraph b) => a -> HGraph b -> HGraph ('(a, i, is) ': b)
a ~> b = (Node a `pointsAtR` b) `Cons` b

infixr 5 :<
data a :< b = a :< b
type Tree a = HGraph (Tree' 0 1 a)
infixr 5 ++
type family x ++ y where
  '[] ++ y = y
  (a ': b) ++ y = a ': b ++ y

type BranchSize = 100
type family Tree' n x a where
  Tree' n x (b :< (c, d)) =
    '(b, n, '[n + 1 * BranchSize ^ x, n + 2 * BranchSize ^ x]) ':
      (Tree' (n + 1 * BranchSize ^ x) (x + 1) c) ++
      (Tree' (n + 2 * BranchSize ^ x) (x + 1) d)
  Tree' n x (b :< (c, d, e)) =
    '(b, n, '[n + 1 * BranchSize ^ x, n + 2 * BranchSize ^ x, n + 3 * BranchSize ^ x]) ':
      (Tree' (n + 1 * BranchSize ^ x) (x + 1) c) ++
      (Tree' (n + 2 * BranchSize ^ x) (x + 1) d) ++
      (Tree' (n + 3 * BranchSize ^ x) (x + 1) e)
  Tree' n x (b :< c :< d) = '(b, n, '[n + 1]) ': Tree' (n + 1) x (c :< d)
  Tree' n x (b :< c) = '(b, n, '[n + 1]) ': '(c, n + 1, '[]) ': '[]
  Tree' n x b = '(b, n, '[]) ': '[]

class TreeConv a b | a -> b where
  tree :: a -> b
-- | Points at nothing
instance TreeConv (HGraph ('(a, n, '[]) ': x)) a where
  tree (a :<: Nil) = a
-- | Branch
instance
  ( TreeConv (HGraph ('(b, m, x) ': z)) i
  , TreeConv (HGraph ('(c, o, y) ': z)) j
  ) =>
  TreeConv (HGraph ('(a, n, '[m, o]) ': '(b, m, x) ': '(c, o, y) ': z)) (a :< (i, j)) where
  tree (a :<: b `Cons` c `Cons` x) = a :< (tree $ b `Cons` x, tree $ c `Cons` x)
instance
  ( TreeConv (HGraph ('(b, m, x) ': q)) i
  , TreeConv (HGraph ('(c, o, y) ': q)) j
  , TreeConv (HGraph ('(d, p, z) ': q)) k
  ) =>
  TreeConv (HGraph ('(a, n, '[m, o, p]) ': '(b, m, x) ': '(c, o, y) ': '(d, p, z) ': q)) (a :< (i, j, k)) where
  tree (a :<: b `Cons` c `Cons` d `Cons` x) = a :< (tree $ b `Cons` x, tree $ c `Cons` x, tree $ d `Cons` x)
-- | Points at wrong thing
instance {-# OVERLAPPABLE #-}
  ( TreeConv (HGraph ('(a, n, '[m]) ': y)) i
  , TreeConv (HGraph ('(b, o, x) ': y)) j
  ) =>
  TreeConv (HGraph ('(a, n, '[m]) ': '(b, o, x) ': y)) (i :< j) where
  tree (a `Cons` b `Cons` c) = tree (a `Cons` c) :< tree (b `Cons` c)
-- | Adjacent
instance
  ( TreeConv (HGraph ('(b, m, x) ': y)) j
  ) =>
  TreeConv (HGraph ('(a, n, '[m]) ': '(b, m, x) ': y)) (a :< j) where
  tree (a :<: b) = a :< tree b


-- @RawGraph@ is required because, without it, we have to provide no-op @PointsAt@ instances for
-- building the @Arbitrary@ graph we hand to @insertGraph@. i.e.
-- @instance (a `PointsAt` Entity b) => a `PointsAt` b where a `pointsAt` _ = a@
-- But then any graphs missing an instance match this instance and fail via a context reduction stack overflow
-- which is pretty ugly.
data RawGraph a = RawGraph { unRawGraph :: HGraph a }

instance Arbitrary (RawGraph '[]) where
  arbitrary = pure $ RawGraph Nil
instance (Arbitrary (Node i ('Right is) a), Arbitrary (RawGraph b)) => Arbitrary (RawGraph ('(a, i, is) ': b)) where
  arbitrary = do
    RawGraph <$> (Cons <$> arbitrary <*> (unRawGraph <$> arbitrary))

instance Arbitrary (HGraph '[]) where
  arbitrary = pure Nil
instance
  (Node i ('Right is) a `PointsAtR` HGraph b, Arbitrary (Node i ('Right is) a), Arbitrary (HGraph b)) =>
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
