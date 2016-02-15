{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

-- | You should try to avoid using this module.
-- It has the raw @PointsTo@ and consequently allows you to construct @:~>:@
-- which aren't actually linked.
module Data.Graph.HGraph.Internal where

import Data.Monoid ((<>))
import Data.Tagged
import Data.Typeable (Typeable)

infixr 5 `Cons`
data HGraph a where
  Cons :: Tagged '((i :: k), (is :: [k])) a -> HGraph b -> HGraph ('(a, i, is) ': b)
  Nil :: HGraph '[]

instance (Show x, Show (HGraph xs)) => Show (HGraph ('(x, i, is) ': xs)) where
  show (Cons x y) = "Cons (" <> show x <> ") (" <> show y <> ")"
instance Show (HGraph '[]) where
  show Nil = "Nil"
instance (Eq x, Eq (HGraph xs)) => Eq (HGraph ('(x, i, is) ': xs)) where
  (Cons x1 xs1) == (Cons x2 xs2) = x1 == x2 && xs1 == xs2
instance Eq (HGraph '[]) where
  Nil == Nil = True
deriving instance Typeable (HGraph a)

type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t
