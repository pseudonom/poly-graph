{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

module Data.Graph.HGraph.Persistent.TH
  ( UniquenessCheck(..)
  , mkUniquenessChecks
  , mkUniquenessCheck
  ) where

import Control.Arrow ((&&&))
import Data.Char (toLower, toUpper)
import Data.List.NonEmpty (nonEmpty)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import Data.Monoid ((<>))
import Data.Text (Text, unpack, cons, uncons)
import Database.Persist
import Database.Persist.TH
import Language.Haskell.TH

class UniquenessCheck a where
  couldCauseUniquenessViolation :: a -> a -> Bool

mkUniquenessChecks :: MkPersistSettings -> [EntityDef] -> Q [Dec]
mkUniquenessChecks settings = fmap concat . traverse (mkUniquenessCheck settings)

mkUniquenessCheck :: MkPersistSettings -> EntityDef -> Q [Dec]
mkUniquenessCheck settings EntityDef{..} =
  [d|
    instance UniquenessCheck $typeName where
      couldCauseUniquenessViolation $lhs $rhs = $expr
  |]
 where
  lhs = pure $ VarP $ mkName "lhs"
  rhs = pure $ VarP $ mkName "rhs"

  unHaskelled = unHaskellName entityHaskell
  typeName = conT $ mkName $ unpack unHaskelled

  nameToRef = Map.fromList ((fieldHaskell &&& fieldReference) <$> entityFields)
  expr = pure $ mkOrExpr mkSelector nameToRef entityUniques

  mkSelector = mkName . unpack . maybeUnderscore . maybePrefixed
  maybeUnderscore fieldName
   | mpsGenerateLenses settings = '_' `cons` fieldName
   | otherwise = fieldName
  maybePrefixed fieldName
   | mpsPrefixFields settings = lowerFirst unHaskelled <> upperFirst (unHaskellName fieldName)
   | otherwise = unHaskellName fieldName

lowerFirst :: Text -> Text
lowerFirst t =
  case uncons t of
    Just (c, cs) -> cons (toLower c) cs
    Nothing -> t

upperFirst :: Text -> Text
upperFirst t =
  case uncons t of
    Just (c, cs) -> cons (toUpper c) cs
    Nothing -> t

mkOrExpr :: (HaskellName -> Name) -> Map HaskellName ReferenceDef -> [UniqueDef] -> Exp
mkOrExpr mkSelector nameToRef uniqueDefs =
  maybe
    false
    (foldl1 $ binApp orOp)
    (nonEmpty andExprs)
 where
  false = ConE $ mkName "False"
  orOp = VarE $ mkName "||"
  andExprs = mapMaybe (mkAndExpr mkSelector nameToRef) uniqueDefs

mkAndExpr :: (HaskellName -> Name) -> Map HaskellName ReferenceDef -> UniqueDef -> Maybe Exp
mkAndExpr mkSelector nameToRef UniqueDef{..} =
  foldl1 (binApp andOp) <$> nonEmpty comparisons
 where
  andOp = VarE $ mkName "&&"
  fields = map fst uniqueFields
  nonForeignFields = filter (not . isForeignRef . (nameToRef Map.!)) fields
  comparisons = map (mkComparison . mkSelector) nonForeignFields

mkComparison :: Name -> Exp
mkComparison selector =
  binApp eqOp (VarE selector `AppE` lhs) (VarE selector `AppE` rhs)
 where
  eqOp = VarE $ mkName "=="
  lhs = VarE $ mkName "lhs"
  rhs = VarE $ mkName "rhs"

binApp :: Exp -> Exp -> Exp -> Exp
binApp f x y = UInfixE x f y

isForeignRef :: ReferenceDef -> Bool
isForeignRef ForeignRef{} = True
isForeignRef _ = False
