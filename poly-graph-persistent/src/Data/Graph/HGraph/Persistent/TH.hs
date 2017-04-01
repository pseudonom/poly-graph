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
mkUniquenessCheck settings def = do
  lhs <- newName "lhs"
  rhs <- newName "rhs"
  mkUniquenessCheckWithOperands settings def (lhs, rhs)

mkUniquenessCheckWithOperands :: MkPersistSettings -> EntityDef -> (Name, Name) -> Q [Dec]
mkUniquenessCheckWithOperands settings EntityDef{..} operands@(lhs, rhs) =
  [d|
    instance UniquenessCheck $typeName where
      couldCauseUniquenessViolation $(varP lhs) $(varP rhs) = $expr
  |]
 where
  unHaskelled = unHaskellName entityHaskell
  typeName = conT $ mkName $ unpack unHaskelled

  nameToRef = Map.fromList ((fieldHaskell &&& fieldReference) <$> entityFields)
  expr = pure $ mkOrExpr mkSelector nameToRef operands entityUniques

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

mkOrExpr :: (HaskellName -> Name) -> Map HaskellName ReferenceDef -> (Name, Name) -> [UniqueDef] -> Exp
mkOrExpr mkSelector nameToRef operands uniqueDefs =
  maybe false (foldl1 $ binApp orOp) (nonEmpty andExprs)
 where
  false = ConE $ mkName "False"
  orOp = VarE $ mkName "||"
  andExprs = mapMaybe (mkAndExpr mkSelector nameToRef operands) uniqueDefs

mkAndExpr :: (HaskellName -> Name) -> Map HaskellName ReferenceDef -> (Name, Name) -> UniqueDef -> Maybe Exp
mkAndExpr mkSelector nameToRef operands UniqueDef{..} =
  foldl1 (binApp andOp) <$> nonEmpty comparisons
 where
  andOp = VarE $ mkName "&&"
  fields = map fst uniqueFields
  nonForeignFields = filter (not . isForeignRef . (nameToRef Map.!)) fields
  comparisons = map (mkComparison operands . mkSelector) nonForeignFields

mkComparison :: (Name, Name) -> Name -> Exp
mkComparison (lhs, rhs) selector =
  binApp eqOp (VarE selector `AppE` VarE lhs) (VarE selector `AppE` VarE rhs)
 where
  eqOp = VarE $ mkName "=="

binApp :: Exp -> Exp -> Exp -> Exp
binApp f x y = UInfixE x f y

isForeignRef :: ReferenceDef -> Bool
isForeignRef ForeignRef{} = True
isForeignRef _ = False
