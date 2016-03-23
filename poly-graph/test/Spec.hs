{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

import Test.Hspec

import Data.Tagged (Tagged(..))

import Data.Graph.HGraph
import Data.Graph.HGraph.Internal (HGraph(Cons))

data Node
  = Node
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
main = hspec $
  describe "~>" $ do
    it "works for simple chains" $
      simpleChain `shouldBe` simpleChain'
    it "works for fan outs" $
      fanOut `shouldBe` fanOut'
    it "works for fan ins" $
      fanIn `shouldBe` fanIn'
    it "works for a complicated mess" $
      inAndOut `shouldBe` inAndOut'

instance Node `PointsAt` Node where
  (Node id1 _) `pointsAt` (Node id2 _) = Node id1 (Just id2)
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
    NodeA :<:
      NodeB :<:
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
  Tagged (NodeA 1 (Just 2)) `Cons`
    Tagged (NodeB 2 (Just 3)) `Cons`
      Tagged (NodeC 3 Nothing Nothing) `Cons`
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
    NodeC :<:
      ( NodeA
      , NodeB :<: NodeC
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
  Tagged (NodeC 1 (Just 2) (Just 3)) `Cons`
    Tagged (NodeA 2 Nothing) `Cons`
    Tagged (NodeB 3 (Just 4)) `Cons`
      Tagged (NodeC 4 Nothing Nothing) `Cons` Nil

-- | Our "read-only" patterns work as expected
deconstruct :: (NodeC, NodeA, NodeB, NodeC)
deconstruct =
  case tree fanOut of
    c1 :<: (a, b :<: c2) -> (c1, a, b, c2)

-- -- | Graph looks like
-- -- @
-- --  C>-------+
-- --           |
-- --           V
-- --           B>------>C
-- --           ^
-- --           |
-- --  A>-------+
-- -- @

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
  Tagged (NodeC 1 Nothing (Just 3)) `Cons`
  Tagged (NodeA 2 (Just 3)) `Cons`
  Tagged (NodeB 3 (Just 4)) `Cons`
  Tagged (NodeC 4 Nothing Nothing) `Cons` Nil

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
  [ '(Node, 1, '[7])
  , '(Node, 2, '[3, 5, 6])
  , '(Node, 3, '[4])
  , '(Node, 4, '[7])
  , '(Node, 5, '[7])
  , '(Node, 6, '[])
  , '(Node, 7, '[])
  ]
inAndOut =
  Node 1 Nothing ~>
  Node 2 Nothing ~>
  Node 3 Nothing ~>
  Node 4 Nothing ~>
  Node 5 Nothing ~>
  Node 6 Nothing ~>
  Node 7 Nothing ~>
  Nil

inAndOut' ::
  HGraph
  [ '(Node, 1, '[7])
  , '(Node, 2, '[3, 5, 6])
  , '(Node, 3, '[4])
  , '(Node, 4, '[7])
  , '(Node, 5, '[7])
  , '(Node, 6, '[])
  , '(Node, 7, '[])
  ]
inAndOut' =
  Tagged (Node 1 (Just 7)) `Cons`
  Tagged (Node 2 (Just 6)) `Cons`
  Tagged (Node 3 (Just 4)) `Cons`
  Tagged (Node 4 (Just 7)) `Cons`
  Tagged (Node 5 (Just 7)) `Cons`
  Tagged (Node 6 Nothing) `Cons`
  Tagged (Node 7 Nothing) `Cons`
  Nil
