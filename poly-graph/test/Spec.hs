{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

import Test.Hspec

import Data.Graph.HGraph
import Data.Graph.HGraph.Internal ((:~>:)(PointsTo))

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

instance Node ~~> Node where
  (Node id1 _) ~~> (Node id2 _) = Node id1 (Just id2)
instance NodeA ~~> NodeB where
  (NodeA ida _) ~~> (NodeB idb _) = NodeA ida (Just idb)
instance NodeB ~~> NodeC where
  (NodeB idb _) ~~> (NodeC idc _ _) = NodeB idb (Just idc)
instance NodeC ~~> NodeA where
  (NodeC idc _ idb) ~~> (NodeA ida _) = NodeC idc (Just ida) idb
instance NodeC ~~> NodeB where
  (NodeC idc ida _) ~~> (NodeB idb _) = NodeC idc ida (Just idb)

simpleChain ::
  NodeA :~>:
    NodeB :~>:
      NodeC
simpleChain =
  NodeA 1 (Just 6) ~>
    NodeB 2 Nothing ~>
      NodeC 3 Nothing Nothing

simpleChain' ::
  NodeA :~>:
    NodeB :~>:
      NodeC
simpleChain' =
  NodeA 1 (Just 2) `PointsTo`
    NodeB 2 (Just 3) `PointsTo`
      NodeC 3 Nothing Nothing

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
-- You could also omit the `ToMany` and just use `(,)`,
-- but `ToMany` makes things more explicit and,
-- I think, clarifies errors when writing these terms.
fanOut ::
  NodeC :~>:
    ToMany
    ( NodeA
    , NodeB :~>:
        NodeC
    )
fanOut =
  NodeC 1 (Just 4) Nothing ~>
    ToMany
    ( NodeA 2 Nothing
    , NodeB 3 Nothing ~>
        NodeC 4 Nothing Nothing
    )

fanOut' ::
  NodeC :~>:
    ToMany
    ( NodeA
    , NodeB :~>:
        NodeC
    )
fanOut' =
  NodeC 1 (Just 2) (Just 3) `PointsTo`
    ToMany
    ( NodeA 2 Nothing
    , NodeB 3 (Just 4) `PointsTo`
        NodeC 4 Nothing Nothing
    )

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
  FromMany
  ( NodeC
  , NodeA
  ) :~>:
    NodeB :~>:
      NodeC
fanIn =
  FromMany
  ( NodeC 1 Nothing Nothing
  , NodeA 2 (Just 1)
  ) ~>
    NodeB 3 (Just 7) ~>
      NodeC 4 Nothing Nothing

fanIn' ::
  FromMany
  ( NodeC
  , NodeA
  ) :~>:
    NodeB :~>:
      NodeC
fanIn' =
  FromMany
  ( NodeC 1 Nothing (Just 3)
  , NodeA 2 (Just 3)
  ) `PointsTo`
    NodeB 3 (Just 4) ~>
      NodeC 4 Nothing Nothing

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
  FromMany
  ( Node
  , Node :~>:
      ToMany
      ( FromTo
        ( Node :~>: Node
        , Node
        )
      , Node
      )
  ) :~>:
    Node
inAndOut =
  FromMany
  ( Node 1 Nothing
  , Node 2 Nothing ~>
      ToMany
      ( FromTo
        ( Node 3 Nothing ~> Node 4 Nothing
        , Node 5 Nothing
        )
      , Node 6 Nothing
      )
  ) ~>
    Node 7 Nothing

inAndOut' ::
  FromMany
  ( Node
  , Node :~>:
      ToMany
      ( FromTo
        ( Node :~>: Node
        , Node
        )
      , Node
      )
  ) :~>:
    Node
inAndOut' =
  FromMany
  ( Node 1 (Just 7)
  , Node 2 (Just 6) `PointsTo` -- If we had multiple pointers, Node 2 would point to 3, 5, 6.
      ToMany                   -- Because I'm lazy, it just points to the final Node.
      ( FromTo
        ( Node 3 (Just 4) `PointsTo` Node 4 (Just 7)
        , Node 5 (Just 7)
        )
      , Node 6 Nothing
      )
  ) `PointsTo`
    Node 7 Nothing
