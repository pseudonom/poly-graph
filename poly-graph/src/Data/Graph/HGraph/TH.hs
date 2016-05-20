{-# LANGUAGE TemplateHaskell #-}
module Data.Graph.HGraph.TH where

import Language.Haskell.TH

import Data.Graph.HGraph
import Data.Proxy

declareBases :: [Name] -> DecsQ
declareBases = fmap concat . mapM declareBase

declareBase :: Name -> DecsQ
declareBase name' =
  [d|
    type instance Base $name = $name
    instance ToBase $name where
      base = id
  |]
  where
    name = conT name'

-- | Shorthand until we get explicit type application
sym :: String -> ExpQ
sym x' = [| Proxy :: Proxy $x |]
  where
    x = litT (strTyLit x')
