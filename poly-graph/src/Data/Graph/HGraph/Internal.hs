{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeOperators #-}

-- | You should try to avoid using this module.
-- It has the raw @PointsTo@ and consequently allows you to construct @:~>:@
-- which aren't actually linked.
module Data.Graph.HGraph.Internal where

import GHC.Generics (Generic)
import Data.Typeable (Typeable)

-- | Represents the edge in a directed graph with nodes @a@ and @b@
infixr 2 :~>:
infixr 2 `PointsTo`
data a :~>: b = a `PointsTo` b deriving (Read, Show, Eq, Ord, Generic, Typeable)
