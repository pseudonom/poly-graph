{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

import Test.Hspec

import Data.Graph.HGraph
import Data.Graph.HGraph.Instances
import Data.Graph.HGraph.Internal (HGraph(Cons))

data SelfNode
  = SelfNode
  { id' :: Int
  , pointer :: Maybe Int
  } deriving (Show, Eq)

newtype IdA = IdA Int deriving (Show, Eq, Num)
data NodeA
  = NodeA
  { idA :: IdA
  , aPointer :: Maybe IdB
  } deriving (Show, Eq)

newtype IdB = IdB Int deriving (Show, Eq, Num)
data NodeB
  = NodeB
  { idB :: IdB
  , bPointer :: Maybe IdC
  } deriving (Show, Eq)

newtype IdC = IdC Int deriving (Show, Eq, Num)
data NodeC
  = NodeC
  { idC :: IdC
  , cPointer1 :: Maybe IdA
  , cPointer2 :: Maybe IdB
  } deriving (Show, Eq)


main :: IO ()
main = hspec $ do
  let -- Make sure we support all combinations
      node = SelfNode 1 (Just 1)
      plainToPlain = node `pointsAt` node
      plainToMaybe = node `pointsAt` Just node
      plainToAlways = node `pointsAt` Always node
      plainToNever = node `pointsAt` (Never :: Never SelfNode)

      maybeToPlain = Just node `pointsAt` node
      maybeToMaybe = Just node `pointsAt` Just node
      maybeToAlways = Just node `pointsAt` Always node
      maybeToNever = Just node `pointsAt` (Never :: Never SelfNode)

      alwaysToPlain = Always node `pointsAt` node
      alwaysToMaybe = Always node `pointsAt` Just node
      alwaysToAlways = Always node `pointsAt` Always node
      alwaysToNever = Always node `pointsAt` (Never :: Never SelfNode)

      neverToPlain = (Never :: Never SelfNode) `pointsAt` node
      neverToMaybe = (Never :: Never SelfNode) `pointsAt` Just node
      neverToAlways = (Never :: Never SelfNode) `pointsAt` Always node
      neverToNever = (Never :: Never SelfNode) `pointsAt` (Never :: Never SelfNode)

  describe "~>" $ do
    it "works for simple chains" $
      simpleChain `shouldBe` simpleChain'
    it "works for fan outs" $
      fanOut `shouldBe` fanOut'
    it "works for fan ins" $
      fanIn `shouldBe` fanIn'
    it "works for a complicated mess" $
      inAndOut `shouldBe` inAndOut'

instance SelfNode `PointsAt` SelfNode where
  (SelfNode id1 _) `pointsAt` (SelfNode id2 _) = SelfNode id1 (Just id2)
instance NodeA `PointsAt` NodeB where
  (NodeA ida _) `pointsAt` (NodeB idb _) = NodeA ida (Just idb)
instance NodeB `PointsAt` NodeC where
  (NodeB idb _) `pointsAt` (NodeC idc _ _) = NodeB idb (Just idc)
instance NodeC `PointsAt` NodeA where
  (NodeC idc _ idb) `pointsAt` (NodeA ida _) = NodeC idc (Just ida) idb
instance NodeC `PointsAt` NodeB where
  (NodeC idc ida _) `pointsAt` (NodeB idb _) = NodeC idc ida (Just idb)

simpleChain ::
  Tree (
    NodeA :<
      NodeB :<
        NodeC
  )
simpleChain =
  NodeA 1 (Just 6) ~>
    NodeB 2 Nothing ~>
      NodeC 3 Nothing Nothing ~>
        Nil

simpleChain' ::
  HGraph
  [ '(NodeA, 0, '[1])
  , '(NodeB, 1, '[2])
  , '(NodeC, 2, '[])
  ]
simpleChain' =
  Node (NodeA 1 (Just 2)) `Cons`
    Node (NodeB 2 (Just 3)) `Cons`
      Node (NodeC 3 Nothing Nothing) `Cons`
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
    NodeC :<
      ( NodeA
      , NodeB :< NodeC
      )
  )
fanOut =
  NodeC 1 (Just 4) Nothing ~>
    NodeA 2 Nothing ~>
    NodeB 3 Nothing ~>
      NodeC 4 Nothing Nothing ~> Nil

fanOut' ::
  HGraph
  [ '(NodeC, 0, '[100, 200])
  , '(NodeA, 100, '[])
  , '(NodeB, 200, '[201])
  , '(NodeC, 201, '[])
  ]
fanOut' =
  Node (NodeC 1 (Just 2) (Just 3)) `Cons`
    Node (NodeA 2 Nothing) `Cons`
    Node (NodeB 3 (Just 4)) `Cons`
      Node (NodeC 4 Nothing Nothing) `Cons` Nil

-- | Our "read-only" patterns work as expected
deconstruct :: (NodeC, NodeA, NodeB, NodeC)
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
  [ '(NodeC, "firstC", '["b"])
  , '(NodeA, "a", '["b"])
  , '(NodeB, "b", '["secondC"])
  , '(NodeC, "secondC", '[])
  ]
fanIn =
  NodeC 1 Nothing Nothing ~>
  NodeA 2 (Just 1) ~>
  NodeB 3 (Just 7) ~>
  NodeC 4 Nothing Nothing ~> Nil

fanIn' ::
  HGraph
  [ '(NodeC, "firstC", '["b"])
  , '(NodeA, "a", '["b"])
  , '(NodeB, "b", '["secondC"])
  , '(NodeC, "secondC", '[])
  ]
fanIn' =
  Node (NodeC 1 Nothing (Just 3)) `Cons`
  Node (NodeA 2 (Just 3)) `Cons`
  Node (NodeB 3 (Just 4)) `Cons`
  Node (NodeC 4 Nothing Nothing) `Cons` Nil

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
  [ '(SelfNode, 1, '[7])
  , '(SelfNode, 2, '[3, 5, 6])
  , '(SelfNode, 3, '[4])
  , '(SelfNode, 4, '[7])
  , '(SelfNode, 5, '[7])
  , '(SelfNode, 6, '[])
  , '(SelfNode, 7, '[])
  ]
inAndOut =
  SelfNode 1 Nothing ~>
  SelfNode 2 Nothing ~>
  SelfNode 3 Nothing ~>
  SelfNode 4 Nothing ~>
  SelfNode 5 Nothing ~>
  SelfNode 6 Nothing ~>
  SelfNode 7 Nothing ~>
  Nil

inAndOut' ::
  HGraph
  [ '(SelfNode, 1, '[7])
  , '(SelfNode, 2, '[3, 5, 6])
  , '(SelfNode, 3, '[4])
  , '(SelfNode, 4, '[7])
  , '(SelfNode, 5, '[7])
  , '(SelfNode, 6, '[])
  , '(SelfNode, 7, '[])
  ]
inAndOut' =
  Node (SelfNode 1 (Just 7)) `Cons`
  Node (SelfNode 2 (Just 6)) `Cons`
  Node (SelfNode 3 (Just 4)) `Cons`
  Node (SelfNode 4 (Just 7)) `Cons`
  Node (SelfNode 5 (Just 7)) `Cons`
  Node (SelfNode 6 Nothing) `Cons`
  Node (SelfNode 7 Nothing) `Cons`
  Nil
