{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Graph.Polymorphic
  ( (:~>:)
  , module Data.Graph.Polymorphic
  ) where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Data.Graph.Polymorphic.Internal

-- | Smart constructor which ensures inhabitants of @:~>:@ are linked
infixr 2 ~>
(~>) :: (a ~~> b) => a -> b -> a :~>: b
a ~> b = (a ~~> b) `PointsTo` b

-- | We need to hide @PointsTo@ to enforce use of the smart constructor.
-- But then we lose the ability to pattern match.
-- We recover it by defining a 'read-only' pattern.
pattern a :~>: b <- a `PointsTo` b

-- | @a ~~> b@ returns an @a@ linked to @b@
class a ~~> b where
  infixl 3 ~~>
  (~~>) :: a -> b -> a

-- | @FromMany (a, b, ...) :~>: c@ indicates that each of @a@, @b@, ... point to @c@
newtype FromMany a = FromMany a deriving (Read, Show, Eq, Ord, Generic, Typeable, Functor)
-- | @a :~>: ToMany (b, c, ...)@ indicates that @a@ points to each of @b@, @c@, ...
newtype ToMany a = ToMany a deriving (Read, Show, Eq, Ord, Generic, Typeable, Functor)
-- | @a :~>: FromTo (b, c, ...) :~>: d@ indicates that
-- @a@ points to each of @b@, @c@, ... which each point to @d@
newtype FromTo a = FromTo a deriving (Read, Show, Eq, Ord, Generic, Typeable, Functor)

instance (a ~~> c, b ~~> c) => (a, b) ~~> c where
  (a, b) ~~> c = (a ~~> c, b ~~> c)
instance (a ~~> d, b ~~> d, c ~~> d) => (a, b, c) ~~> d where
  (a, b, c) ~~> d = (a ~~> d, b ~~> d, c ~~> d)
instance (a ~~> e, b ~~> e, c ~~> e, d ~~> e) => (a, b, c, d) ~~> e where
  (a, b, c, d) ~~> e = (a ~~> e, b ~~> e, c ~~> e, d ~~> e)
instance (a ~~> b, a ~~> c) => a ~~> (b, c) where
  a ~~> (b, c) = a ~~> b ~~> c
instance (a ~~> b, a ~~> c, a ~~> d) => a ~~> (b, c, d) where
  a ~~> (b, c, d) = a ~~> b ~~> c ~~> d
instance (a ~~> b, a ~~> c, a ~~> d, a ~~> e) => a ~~> (b, c, d, e) where
  a ~~> (b, c, d, e) = a ~~> b ~~> c ~~> d ~~> e
instance {-# OVERLAPPABLE #-} (a ~~> b, Functor f) => f a ~~> b where
  as ~~> b = (~~> b) <$> as

instance (a ~~> b) => a ~~> (b :~>: c) where
  a ~~> (b `PointsTo` _) = a ~~> b
instance (a ~~> b, b ~~> c) => (a :~>: b) ~~> c where
  (a `PointsTo` b) ~~> c = a ~> (b ~~> c)

instance (a ~~> b) => FromMany a ~~> b where
  FromMany a ~~> b = FromMany $ a ~~> b
instance (a ~~> b) => a ~~> ToMany b where
  a ~~> ToMany b = a ~~> b
instance (a ~~> b) => a ~~> FromTo b where
  a ~~> FromTo b = a ~~> b
instance (a ~~> b) => FromTo a ~~> b where
  FromTo a ~~> b = FromTo $ a ~~> b

instance (FromTo a ~~> c) => ToMany ((FromTo a), b) ~~> c where
  (ToMany (FromTo a, b)) ~~> c = ToMany (FromTo a ~~> c, b)
instance (FromTo b ~~> c) => ToMany (a, (FromTo b)) ~~> c where
  (ToMany (a, FromTo b)) ~~> c = ToMany (a, FromTo b ~~> c)

instance {-# OVERLAPPING #-} (a ~~> b) => FromMany a ~~> (b :~>: c) where
  FromMany a ~~> (b `PointsTo` _) = FromMany (a ~~> b)

-- | For use with e.g. @Control.Lens@
-- Don't abuse them by updating the pointer field
type Lens s t a b = forall f. Functor f => (a -> f b) -> (s -> f t)

parent :: Lens (a :~>: b) (c :~>: b) a c
parent f (a `PointsTo` b) = (`PointsTo` b) <$> f a
child :: Lens (a :~>: b) (a :~>: c) b c
child f (a `PointsTo` b) = (a `PointsTo`) <$> f b
fromMany :: Lens (FromMany a) (FromMany b) a b
fromMany f (FromMany a) = FromMany <$> f a
toMany :: Lens (ToMany a) (ToMany b) a b
toMany f (ToMany a) = ToMany <$> f a
fromTo :: Lens (FromTo a) (FromTo b) a b
fromTo f (FromTo a) = FromTo <$> f a
