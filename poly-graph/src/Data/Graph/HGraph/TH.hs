{-# LANGUAGE TemplateHaskell #-}
module Data.Graph.HGraph.TH where

import Language.Haskell.TH

import Data.Graph.HGraph

declareBases :: [Name] -> DecsQ
declareBases = fmap concat . mapM declareBase

declareBase :: Name -> DecsQ
declareBase name' =
  [d|
    type instance Base $(name) = $(name)
    instance ToBase $(name) where
      base = id
  |]
  where
    name = conT name'
