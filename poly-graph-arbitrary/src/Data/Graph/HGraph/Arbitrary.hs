{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- Pattern synonyms and exhuastivity checking don't work well together
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Make @Arbitrary@ polymorphic graphs
module Data.Graph.HGraph.Arbitrary where

import Data.Functor.Identity
import Data.Proxy
import Data.Tagged
import Test.QuickCheck.Arbitrary

import Data.Graph.HGraph

type Never = Proxy
type Always = Identity

pattern Always a = Identity a
pattern Never = Proxy

instance (Arbitrary a) => Arbitrary (Always a) where
  arbitrary = Always <$> arbitrary
instance Arbitrary (Never a) where
  arbitrary = pure Never
instance (a `Link` b) => (Always a) `Link` b where
  (Always a) `link` b = Always $ a `link` b
instance (a `Link` (Maybe b)) => a `Link` (Never b) where
  a `link` Never = a `link` (Nothing :: Maybe b)
instance (a `Link` Maybe b) => a `Link` (Always b) where
  a `link` (Always b) = a `link` Just b
instance (a `Link` Maybe b) => (Always a) `Link` (Always b) where
  a `link` (Always b) = a `link` Just b
instance (a `Link` Maybe b) => (Always a) `Link` (Never b) where
  (Always a) `link` Never = Always $ a `link` (Nothing :: Maybe b)

instance Arbitrary (HGraph '[]) where
  arbitrary = pure Nil
instance
  (Tagged '(i, is) a `LinkR` HGraph b, Arbitrary a, Arbitrary (HGraph b)) =>
  Arbitrary (HGraph ('(a, i, is) ': b)) where
  arbitrary = (~>) <$> arbitrary <*> arbitrary
