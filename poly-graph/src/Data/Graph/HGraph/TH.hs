{-# LANGUAGE TemplateHaskell #-}
module Data.Graph.HGraph.TH where

import Language.Haskell.TH

import Data.Graph.HGraph

declareBases :: [Name] -> DecsQ
declareBases = fmap concat . mapM declareBase

declareBase :: Name -> DecsQ
declareBase name =
  [d|
    instance ToBase $(name') where
      type HasBase $(name') = 'True
      type Base $(name') = $(name')
      base = id
  |]
  where
    name' = conT name

-- mkClassP :: Name -> [Type] -> Pred
-- mkClassP cla tys = foldl AppT (ConT cla) tys
