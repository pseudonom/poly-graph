{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Make @Arbitrary@ polymorphic graphs
module Data.Graph.HGraph.Arbitrary where

import Data.DeriveTH
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Test.QuickCheck.Arbitrary

import Data.Graph.HGraph

-- | Control linking behavior when linking is optional i.e. never link
data Never a = Never deriving (Read, Show, Eq, Ord, Generic, Typeable, Functor)
$(derive makeArbitrary ''Never)
-- | Control linking behavior when linking is optional i.e. always link
data Always a = Always { unAlways :: a } deriving (Read, Show, Eq, Ord, Generic, Typeable, Functor)
$(derive makeArbitrary ''Always)

$(derive makeArbitrary ''FromMany)
$(derive makeArbitrary ''ToMany)
$(derive makeArbitrary ''FromTo)

instance (a ~~> b) => Always a ~~> b where
  Always a ~~> b = Always $ a ~~> b
instance (a ~~> Maybe b) => a ~~> Never b where
  a ~~> Never = a ~~> (Nothing :: Maybe b)
instance (a ~~> Maybe b) => a ~~> Always b where
  a ~~> Always b = a ~~> Just b
instance {-# OVERLAPPING #-} (a ~~> Maybe b) => Always a ~~> Always b where
  Always a ~~> Always b = Always $ a ~~> Just b

instance (a ~~> b, Arbitrary a, Arbitrary b) => Arbitrary (a :~>: b) where
  arbitrary = (~>) <$> arbitrary <*> arbitrary
