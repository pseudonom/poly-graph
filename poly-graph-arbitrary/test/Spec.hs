{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

import Data.DeriveTH (derive, makeArbitrary)
import Test.Hspec (hspec, describe, shouldBe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck.Arbitrary (Arbitrary(..))
import Test.QuickCheck.Gen (Gen, generate)

import Data.Graph.HGraph
import Data.Graph.HGraph.Arbitrary

data Node
  = Node
  { id' :: Int
  , pointer :: Maybe Int
  } deriving (Show, Eq)
$(derive makeArbitrary ''Node)
instance Node ~~> Maybe Node where
  (Node id1 _) ~~> n2 = Node id1 $ id' <$> n2

main :: IO ()
main = do
  print =<< generate (arbitrary :: Gen (Node :~>: Maybe Node))
  hspec $
    describe "Arbitrary" $ do
      prop "`Always` always links" $ \(x :~>: Always y) ->
        pointer x `shouldBe` Just (id' y)
      prop "`Never` never links" $ \(x :~>: (Never :: Never Node)) ->
        pointer x `shouldBe` Nothing
