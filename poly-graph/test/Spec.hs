{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

import Test.Hspec

import Data.Tagged
import GHC.Generics

import Data.Graph.HGraph
import Data.Graph.HGraph.Instances
import Data.Graph.HGraph.Internal (HGraph(Cons))

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

instance
  {-# OVERLAPPABLE #-}
  (b `GPointsAt` c) =>
  (a, b) `GPointsAt` c where
  (a, b) `gPointsAt` c = (a, b `gPointsAt` c)
instance
  {-# OVERLAPPABLE #-}
  (GNullify b) =>
  GNullify (a, b) where
  gNullify (a, b) = (a, gNullify b)

main :: IO ()
main = hspec $ do
  let -- Make sure we support all combinations
      node = Node1 (Tagged 1) (Just $ Tagged 1) :: Node1 'Self 'Self
      plainToPlain = node `pointsAt` node
      plainToMaybe = node `pointsAt` Just node
      plainToAlways = node `pointsAt` Always node
      plainToNever = node `pointsAt` (Never :: Never (Node1 'Self 'Self))

      maybeToPlain = Just node `pointsAt` node
      maybeToMaybe = Just node `pointsAt` Just node
      maybeToAlways = Just node `pointsAt` Always node
      maybeToNever = Just node `pointsAt` (Never :: Never (Node1 'Self 'Self))

      alwaysToPlain = Always node `pointsAt` node
      alwaysToMaybe = Always node `pointsAt` Just node
      alwaysToAlways = Always node `pointsAt` Always node
      alwaysToNever = Always node `pointsAt` (Never :: Never (Node1 'Self 'Self))

      neverToPlain = (Never :: Never (Node1 'Self 'Self)) `pointsAt` node
      neverToMaybe = (Never :: Never (Node1 'Self 'Self)) `pointsAt` Just node
      neverToAlways = (Never :: Never (Node1 'Self 'Self)) `pointsAt` Always node
      neverToNever = (Never :: Never (Node1 'Self 'Self)) `pointsAt` (Never :: Never (Node1 'Self 'Self))

  describe "~>" $ do
    it "works for simple chains" $
      simpleChain `shouldBe` simpleChain'
    it "works for fan outs" $
      fanOut `shouldBe` fanOut'
    it "works for fan ins" $
      fanIn `shouldBe` fanIn'
    it "works for a complicated mess" $
      inAndOut `shouldBe` inAndOut'

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

simpleChain ::
  Tree (
    Node1 'A 'B :<
      Node1 'B 'C :<
        Node2 'C 'A 'B
  )
simpleChain =
  Node1 1 (Just 6) ~>
    Node1 2 Nothing ~>
      Node2 3 Nothing Nothing ~>
        Nil

simpleChain' ::
  HGraph
  [ '(Node1 'A 'B, 0, '[1])
  , '(Node1 'B 'C, 1, '[2])
  , '(Node2 'C 'A 'B, 2, '[])
  ]
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
  Tree (
    Node2 'C 'A 'B :<
      ( Node1 'A B
      , Node1 'B 'C :< Node2 'C 'A B
      )
  )
fanOut =
  Node2 1 (Just 4) Nothing ~>
    Node1 2 Nothing ~>
    Node1 3 Nothing ~>
      Node2 4 Nothing Nothing ~> Nil

fanOut' ::
  HGraph
  [ '(Node2 'C 'A 'B, 0, '[100, 200])
  , '(Node1 'A 'B, 100, '[])
  , '(Node1 'B 'C, 200, '[201])
  , '(Node2 'C 'A 'B, 201, '[])
  ]
fanOut' =
  Node (Node2 1 (Just 2) (Just 3)) `Cons`
    Node (Node1 2 Nothing) `Cons`
    Node (Node1 3 (Just 4)) `Cons`
      Node (Node2 4 Nothing Nothing) `Cons` Nil

-- | Our "read-only" patterns work as expected
deconstruct :: (Node2 'C 'A 'B, Node1 'A 'B, Node1 'B 'C, Node2 'C 'A B)
deconstruct =
  case tree fanOut of
    c1 :< (a, b :< c2) -> (c1, a, b, c2)

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
  [ '(Node2 'C 'A 'B, "firstC", '["b"])
  , '(Node1 'A 'B, "a", '["b"])
  , '(Node1 'B 'C, "b", '["secondC"])
  , '(Node2 'C 'A 'B, "secondC", '[])
  ]
fanIn =
  Node2 1 Nothing Nothing ~>
  Node1 2 (Just 1) ~>
  Node1 3 (Just 7) ~>
  Node2 4 Nothing Nothing ~> Nil

fanIn' ::
  HGraph
  [ '(Node2 'C 'A 'B, "firstC", '["b"])
  , '(Node1 'A 'B, "a", '["b"])
  , '(Node1 'B 'C, "b", '["secondC"])
  , '(Node2 'C 'A 'B, "secondC", '[])
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
  [ '(Node1 'Self 'Self, 1, '[7])
  , '(Node1 'Self 'Self, 2, '[3, 5, 6])
  , '(Node1 'Self 'Self, 3, '[4])
  , '(Node1 'Self 'Self, 4, '[7])
  , '(Node1 'Self 'Self, 5, '[7])
  , '(Node1 'Self 'Self, 6, '[])
  , '(Node1 'Self 'Self, 7, '[])
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
  [ '(Node1 'Self 'Self, 1, '[7])
  , '(Node1 'Self 'Self, 2, '[3, 5, 6])
  , '(Node1 'Self 'Self, 3, '[4])
  , '(Node1 'Self 'Self, 4, '[7])
  , '(Node1 'Self 'Self, 5, '[7])
  , '(Node1 'Self 'Self, 6, '[])
  , '(Node1 'Self 'Self, 7, '[])
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
