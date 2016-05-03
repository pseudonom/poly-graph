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
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Graph.HGraph
  ( module Data.Graph.HGraph
  , X.HGraph(Nil)
  , X._head
  , X._tail
  , X.Node(..)
  , X.retag
  ) where

import Data.Functor.Identity
import Data.Type.Bool
import Data.Type.Equality
import Data.Proxy
import Generics.Eot (Void, fromEot, toEot, Eot, HasEot)
import Test.QuickCheck.Arbitrary

import Data.Graph.HGraph.Internal as X

-- | This class specifies how to link two types to reflect their type level linkage in an @HGraph@.
infixr 5 `PointsAt`
class a `PointsAt` b where
  infixr 5 `pointsAt`
  pointsAt :: a -> b -> a
  default pointsAt :: (HasEot a, Eot a `GPointsAt` b) => a -> b -> a
  pointsAt a b = fromEot $ toEot a `gPointsAt` b

-- | This class provides the @Generic@ default implementation of @PointsAt@.
-- We provide the basic recursive structure here to save the end user some boilerplate.
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

-- | This defines the actual interesting behavior happens in our @Generic@ implementation of @PointsAt@.
class FieldPointsAt a b where
  fieldPointsAt :: a -> b -> a

-- | "Read-only" pattern allows convenient destructuring while encouraging preservation
-- linkage invariant
infixr 5 :<
pattern (:<) :: Member i b ~ 'UniqueName => a -> HGraph b -> HGraph ('(i, is, a) ': b)
pattern a :< b <- Node a `Cons` b

-- | We don't strictly need @pointedFrom@ but it makes our errors much more helpful.
class Nullify (pointedFrom :: *) (pointedTo :: *) where
  nullify :: Proxy pointedFrom -> pointedTo -> pointedTo

-- | Handles early escape from @NullifyRecurse@.
class EscapeNullify (pointedFrom :: *) (match :: Bool) (a :: *) where
  escapeNullify :: Proxy pointedFrom -> Proxy match -> a -> a
-- | If we previously set this @Nullable@, leave it alone and terminate recursion.
instance EscapeNullify pointedFrom 'True a where
  escapeNullify Proxy Proxy = id
-- | If we didn't previously set this @Nullable@, @nullify@ is still a possibility.
-- Continue the recursion to see if we do actually get to @nullify@.
instance
  (Nullify pointedFrom a) =>
  EscapeNullify pointedFrom 'False a where
  escapeNullify p Proxy a = nullify p a

type family BaseMember (a :: *) (as :: [*]) :: Bool where
  BaseMember b '[] = 'False
  BaseMember b (a ': as) = If (Base b == Base a) 'True (BaseMember b as)

-- | Uses the list of completed linkages to determine if this key should be nullable.
-- For example, if we've already done @A `PointsAt` Entity B@, we shouldn't wipe @A@'s key to @B@.
class NullifyRecurse (pointedFrom :: *) (completedLinkages :: [*]) (a :: *) where
  nullifyRecurse :: Proxy pointedFrom -> Proxy completedLinkages -> a -> a
-- | There's at least one more linkage left to examine.
-- Test if the candidate @Nullable@ equals the current link and call the corresponding @EscapeNullify@.
instance
  (BaseMember a completedLinkages ~ match, EscapeNullify pointedFrom match a) =>
  NullifyRecurse (pointedFrom :: *) (completedLinkages :: [*]) (a :: *) where
  nullifyRecurse _ Proxy = escapeNullify (Proxy :: Proxy pointedFrom) (Proxy :: Proxy match)

-- | This provides the basic structure of @eot@ recursion so end users don't have to worry about it.
-- Users only have to define the @Nullify@ instances.
class GNullify (original :: *) (typesLinked :: [*]) (a :: *) where
  gNullify :: Proxy original -> Proxy typesLinked -> a -> a
instance (GNullify original typesLinked a, GNullify original typesLinked b) => GNullify original typesLinked (Either a b) where
  gNullify og tl (Left a) = Left $ gNullify og tl a
  gNullify og tl (Right b) = Right $ gNullify og tl b
instance (NullifyRecurse original typesLinked a, GNullify original typesLinked b) => GNullify original typesLinked (a, b) where
  gNullify og tl (a, b) = (nullifyRecurse og tl a, gNullify og tl b)
instance GNullify og ps () where
  gNullify Proxy Proxy () = ()
instance GNullify og ps Void where
  gNullify = error "impossible"

-- | You'd think this is a totally pointless type class and you could just lift @pointsAtR@ to a top-level function.
-- For some reason you can't. GHC complains about ambiguous type variables if you do.
class PointsAtR (i :: k) (is :: [k]) a (b :: [(k, [k], *)]) where
  pointsAtR :: Node i is a -> HGraph b -> Node i is a
instance (PointsAtRInternal is '[] i is a graph) => PointsAtR i is a graph where
  pointsAtR = pointsAtRInternal (Proxy :: Proxy is) (Proxy :: Proxy '[])

class PointsAtRInternal
  (originalLinks :: [k])
  (typesLinked :: [*])
  (i :: k)
  (remainingLinks :: [k])
  (a :: *)
  (graph :: [(k, [k], *)])
  where
  pointsAtRInternal :: Proxy originalLinks -> Proxy typesLinked -> Node i remainingLinks a -> HGraph graph -> Node i remainingLinks a

type Never = Proxy
type Always = Identity

pattern Always :: a -> Always a
pattern Always a = Identity a
pattern Never :: Never a
pattern Never = Proxy

_Always :: Lens' (Always a) a
_Always pure' (Always a) = Always <$> pure' a

_Never :: Lens' (Never a) a
_Never pure' Never = const Never <$> (pure' undefined)

-- | We split out the type family because we can't create the optic for some types. For example, @Lens' (Key a) a@.
type family Base (a :: *) :: *

type instance Base (Maybe a) = Base a
instance (ToBase a) => ToBase (Maybe a) where
  base = _Just . base

type instance Base (Always a) = Base a
instance (ToBase a) => ToBase (Always a) where
  base = _Always . base

type instance Base (Never a) = Base a
instance (ToBase a) => ToBase (Never a) where
  base = _Never . base

class ToBase a where
  base :: Traversal' a (Base a)

_Node :: Lens' (Node i is a) a
_Node pure' (Node a) = Node <$> pure' a

type instance Base (Node i is a) = Base a
instance (ToBase a) => ToBase (Node i is a) where
  base = _Node . base

-- | Base case. Doesn't point at anything.
instance (ToBase a, Base a ~ b, HasEot b, GNullify a typesLinked (Eot b)) =>
  PointsAtRInternal originalLinks typesLinked i '[] a graph where
  pointsAtRInternal Proxy Proxy n _ =
    n & _Node . base %~ fromEot . gNullify (Proxy :: Proxy a) (Proxy :: Proxy typesLinked) . toEot

-- | Points at wrong thing
instance
  (PointsAtRInternal originalLinks typesLinked i (link ': remainingLinks) a graph) =>
  PointsAtRInternal originalLinks typesLinked i (link ': remainingLinks) a ('(j, js, b) ': graph) where
  pointsAtRInternal ol tl a (Cons _ c) = pointsAtRInternal ol tl a c

type family Snoc (as :: [k]) (a :: k) :: [k] where
  Snoc '[] a = '[a]
  Snoc (a ': as) b = a ': (as `Snoc` b)

-- | Adjacent
instance {-# OVERLAPPING #-}
  ( Node i (link ': remainingLinks) a `PointsAt` Node link js b
  , PointsAtRInternal originalLinks (typesLinked `Snoc` b) i remainingLinks a c
  ) =>
  PointsAtRInternal originalLinks typesLinked i (link ': remainingLinks) a ('(link, js, b) ': c) where
  pointsAtRInternal ol Proxy a (Cons b c) = retag $ pointsAtRInternal ol (Proxy :: Proxy (typesLinked `Snoc` b)) a' c
    where
      a' :: Node i remainingLinks a
      a' = retag $ a `pointsAt` b

infixr 5 ~>
(~>) ::
  ((i `Member` b) ~ 'UniqueName, PointsAtRInternal is '[] i is a b) =>
  a -> HGraph b -> HGraph ('(i, is, a) ': b)
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
  ((i `Member` b) ~ 'UniqueName, Arbitrary (Node i is a), Arbitrary (RawGraph b)) =>
  Arbitrary (RawGraph ('(i, is, a) ': b)) where
  arbitrary = do
    RawGraph <$> (Cons <$> arbitrary <*> (unRawGraph <$> arbitrary))

instance Arbitrary (HGraph '[]) where
  arbitrary = pure Nil
instance
  ( (i `Member` b) ~ 'UniqueName
  , PointsAtRInternal is '[] i is a b
  , Arbitrary (Node i is a), Arbitrary (HGraph b)
  ) =>
  Arbitrary (HGraph ('(i, is, a) ': b)) where
  arbitrary = do
    b <- arbitrary
    a <- arbitrary
    pure $ (a `pointsAtR` b) `Cons` b


class Pluck name a b | name a -> b where
  pluck :: Proxy name -> Lens' (HGraph a) b
instance {-# OVERLAPPING #-} Pluck name ('(name, is, b) ': c) b where
  pluck Proxy = _head
instance (Pluck name d b) => Pluck name ('(otherName, is, c) ': d) b where
  pluck p = _tail . pluck p


type Line as = HGraph (Line' as)

type family Line' (as :: [*]) :: [(*, [*], *)] where
  Line' '[k] = '[Ty k '[]]
  Line' (k ': l ': m) = Ty k '[l] ': Line' (l ': m)

type Ty a b = '(a, b, a)
