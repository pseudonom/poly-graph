{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

import Test.Hspec

import Data.Tagged
import Data.Proxy
import GHC.Generics

import Data.Graph.HGraph
import Data.Graph.HGraph.Instances
import Data.Graph.HGraph.Internal (HGraph(Cons))
import Data.Graph.HGraph.TH

data Typ = Self | A | B | C
data Node1 (self :: Typ) (other :: Typ)
  = Node1
  { ident1 :: Tagged self Int
  , pointer :: Maybe (Tagged other Int)
  } deriving (Show, Eq, Generic)
data Node2 (self :: Typ) (other1 :: Typ) (other2 :: Typ)
  = Node2
  { ident2 :: Tagged self Int
  , pointer1 :: Maybe (Tagged other1 Int)
  , pointer2 :: Maybe (Tagged other2 Int)
  } deriving (Show, Eq, Generic)

instance a `FieldPointsAt` b where
  fieldPointsAt = const
instance Nullify pointedFrom pointedTo where
  nullify Proxy = id

instance Normalize (Node1 a b) where
  type NormalizedT (Node1 a b) = Node1 a b
  normalize = id
instance (a `PointsAt` Node1 b c) => PointsAtInternal NoTyCon a (Node1 b c) where
  pointsAtInternal Proxy a b = a `pointsAt` b
instance Normalize (Node2 a b c) where
  type NormalizedT (Node2 a b c) = Node2 a b c
  normalize = id
instance (a `PointsAt` Node2 b c d) => PointsAtInternal NoTyCon a (Node2 b c d) where
  pointsAtInternal Proxy a b = a `pointsAt` b

type instance Base (Tagged t a) = a

type instance Base (Node1 a b) = Node1 a b
instance ToBase (Node1 a b) where
  base = id
type instance Base (Node2 a b c) = Node2 a b c
instance ToBase (Node2 a b c) where
  base = id

main :: IO ()
main = hspec $ do
  let -- Make sure we support all combinations
      node = Node1 (Tagged 1) (Just $ Tagged 1) :: Node1 'Self 'Self
      plainToPlain = node `pointsAtDispatcher` node
      plainToMaybe = node `pointsAtDispatcher` Just node
      plainToAlways = node `pointsAtDispatcher` Always node
      plainToNever = node `pointsAtDispatcher` (Never :: Never (Node1 'Self 'Self))

      maybeToPlain = Just node `pointsAtDispatcher` node
      maybeToMaybe = Just node `pointsAtDispatcher` Just node
      maybeToAlways = Just node `pointsAtDispatcher` Always node
      maybeToNever = Just node `pointsAtDispatcher` (Never :: Never (Node1 'Self 'Self))

      alwaysToPlain = Always node `pointsAtDispatcher` node
      alwaysToMaybe = Always node `pointsAtDispatcher` Just node
      alwaysToAlways = Always node `pointsAtDispatcher` Always node
      alwaysToNever = Always node `pointsAtDispatcher` (Never :: Never (Node1 'Self 'Self))

      neverToPlain = (Never :: Never (Node1 'Self 'Self)) `pointsAtDispatcher` node
      neverToMaybe = (Never :: Never (Node1 'Self 'Self)) `pointsAtDispatcher` Just node
      neverToAlways = (Never :: Never (Node1 'Self 'Self)) `pointsAtDispatcher` Always node
      neverToNever = (Never :: Never (Node1 'Self 'Self)) `pointsAtDispatcher` (Never :: Never (Node1 'Self 'Self))

  describe "~>" $ do
    it "works for simple chains" $
      simpleChain `shouldBe` simpleChain'
    it "works for fan outs" $
      fanOut `shouldBe` fanOut'
    it "works for fan ins" $
      fanIn `shouldBe` fanIn'
    it "works for a complicated mess" $
      inAndOut `shouldBe` inAndOut'

instance Node1 'Self 'Self `PointsAt` Maybe (Node1 'Self 'Self) where
  (Node1 id1 _) `pointsAt` Just (Node1 id2 _) = Node1 id1 (Just id2)
  (Node1 id1 _) `pointsAt` Nothing = Node1 id1 Nothing
instance Node1 'Self 'Self `PointsAt` Node1 'Self 'Self where
  (Node1 id1 _) `pointsAt` (Node1 id2 _) = Node1 id1 (Just id2)
instance Node1 'A 'B `PointsAt` Node1 'B 'C where
  (Node1 ida _) `pointsAt` (Node1 idb _) = Node1 ida (Just idb)
instance Node1 'B 'C `PointsAt` Node2 'C 'A 'B where
  (Node1 idb _) `pointsAt` (Node2 idc _ _) = Node1 idb (Just idc)
instance Node2 'C 'A 'B `PointsAt` Node1 'A 'B where
  (Node2 idc _ idb) `pointsAt` (Node1 ida _) = Node2 idc (Just ida) idb
instance Node2 'C 'A 'B `PointsAt` Node1 'B 'C where
  (Node2 idc ida _) `pointsAt` (Node1 idb _) = Node2 idc ida (Just idb)

simpleChain :: Line '[Node1 'A 'B, Node1 'B 'C, Node2 'C 'A 'B]
simpleChain =
  Node1 1 (Just 6) ~>
    Node1 2 Nothing ~>
      Node2 3 Nothing Nothing ~>
        Nil

simpleChain' :: Line '[Node1 'A 'B, Node1 'B 'C, Node2 'C 'A 'B]
simpleChain' =
  Node (Node1 1 (Just 2)) `Cons`
    Node (Node1 2 (Just 3)) `Cons`
      Node (Node2 3 Nothing Nothing) `Cons`
        Nil

-- | Graph looks like
-- @
-- +----->A
-- |
-- ^
-- C
-- V
-- |
-- +----->B>----->C
-- @
fanOut ::
  HGraph
    '[ '("C1", '["A", "B"], Node2 'C 'A 'B)
     , '("A", '[], Node1 'A 'B)
     , '("B", '["C2"], Node1 'B 'C)
     , '("C2", '[], Node2 'C 'A 'B)
     ]
fanOut =
  Node2 1 (Just 4) Nothing ~>
    Node1 2 Nothing ~>
    Node1 3 Nothing ~>
      Node2 4 Nothing Nothing ~> Nil

fanOut' ::
  HGraph
    '[ '("C1", '["A", "B"], Node2 'C 'A 'B)
     , '("A", '[], Node1 'A 'B)
     , '("B", '["C2"], Node1 'B 'C)
     , '("C2", '[], Node2 'C 'A 'B)
     ]
fanOut' =
  Node (Node2 1 (Just 2) (Just 3)) `Cons`
    Node (Node1 2 Nothing) `Cons`
    Node (Node1 3 (Just 4)) `Cons`
      Node (Node2 4 Nothing Nothing) `Cons` Nil

-- | Graph looks like
-- @
--  C>-------+
--           |
--           V
--           B>------>C
--           ^
--           |
--  A>-------+
-- @

fanIn ::
  HGraph
   '[ '("firstC", '["b"], Node2 'C 'A 'B)
    , '("a", '["b"], Node1 'A 'B)
    , '("b", '["secondC"], Node1 'B 'C)
    , '("secondC", '[], Node2 'C 'A 'B)
    ]
fanIn =
  Node2 1 Nothing Nothing ~>
  Node1 2 (Just 1) ~>
  Node1 3 (Just 7) ~>
  Node2 4 Nothing Nothing ~> Nil

fanIn' ::
  HGraph
   '[ '("firstC", '["b"], Node2 'C 'A 'B)
    , '("a", '["b"], Node1 'A 'B)
    , '("b", '["secondC"], Node1 'B 'C)
    , '("secondC", '[], Node2 'C 'A 'B)
    ]
fanIn' =
  Node (Node2 1 Nothing (Just 3)) `Cons`
  Node (Node1 2 (Just 3)) `Cons`
  Node (Node1 3 (Just 4)) `Cons`
  Node (Node2 4 Nothing Nothing) `Cons` Nil

-- | Graph looks like
-- @
--  +------->5        1>------+
--  |        V                |
--  |        |                |
--  |        +---------------+|
--  |                        ||
--  ^                        VV
--  2>------>3>------>4>----->7
--  V
--  |
--  |
--  +------->6
-- @
inAndOut ::
  HGraph
  [ '(1, '[7], Node1 'Self 'Self)
  , '(2, '[3, 5, 6], Node1 'Self 'Self)
  , '(3, '[4], Node1 'Self 'Self)
  , '(4, '[7], Node1 'Self 'Self)
  , '(5, '[7], Node1 'Self 'Self)
  , '(6, '[], Node1 'Self 'Self)
  , '(7, '[], Node1 'Self 'Self)
  ]
inAndOut =
  Node1 1 Nothing ~>
  Node1 2 Nothing ~>
  Node1 3 Nothing ~>
  Node1 4 Nothing ~>
  Node1 5 Nothing ~>
  Node1 6 Nothing ~>
  Node1 7 Nothing ~>
  Nil

inAndOut' ::
  HGraph
  [ '(1, '[7], Node1 'Self 'Self)
  , '(2, '[3, 5, 6], Node1 'Self 'Self)
  , '(3, '[4], Node1 'Self 'Self)
  , '(4, '[7], Node1 'Self 'Self)
  , '(5, '[7], Node1 'Self 'Self)
  , '(6, '[], Node1 'Self 'Self)
  , '(7, '[], Node1 'Self 'Self)
  ]
inAndOut' =
  Node (Node1 1 (Just 7)) `Cons`
  Node (Node1 2 (Just 6)) `Cons`
  Node (Node1 3 (Just 4)) `Cons`
  Node (Node1 4 (Just 7)) `Cons`
  Node (Node1 5 (Just 7)) `Cons`
  Node (Node1 6 Nothing) `Cons`
  Node (Node1 7 Nothing) `Cons`
  Nil
