{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

import Data.DeriveTH
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen

import Data.Graph.Polymorphic
import Data.Graph.Polymorphic.Arbitrary

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
