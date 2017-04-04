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
import Database.Persist.Quasi (nullable)
import Database.Persist.TH
import Language.Haskell.TH

class UniquenessCheck a where
  couldCauseUniquenessViolation :: a -> a -> Bool

mkUniquenessChecks :: MkPersistSettings -> [EntityDef] -> Q [Dec]
mkUniquenessChecks settings = fmap concat . traverse (mkUniquenessCheck settings)

mkUniquenessCheck :: MkPersistSettings -> EntityDef -> Q [Dec]
mkUniquenessCheck settings def = do
  lhs <- newName "_lhs"
  rhs <- newName "_rhs"
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
  fieldMap = mkFieldMap entityFields

  expr = pure $ mkOrExpr mkSelector fieldMap operands entityUniques

  mkSelector = mkName . unpack . maybeUnderscore . maybePrefixed
  maybeUnderscore fieldName
   | mpsGenerateLenses settings = '_' `cons` fieldName
   | otherwise = fieldName
  maybePrefixed fieldName
   | mpsPrefixFields settings = lowerFirst unHaskelled <> upperFirst (unHaskellName fieldName)
   | otherwise = unHaskellName fieldName

type FieldMap = Map HaskellName (ReferenceDef, IsNullable)

mkFieldMap :: [FieldDef] -> FieldMap
mkFieldMap =
  Map.fromList . map mkPair
 where
  mkPair FieldDef{..} =
    (fieldHaskell, (fieldReference, nullable fieldAttrs))

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

mkOrExpr :: (HaskellName -> Name) -> FieldMap -> (Name, Name) -> [UniqueDef] -> Exp
mkOrExpr mkSelector fieldMap operands uniqueDefs =
  maybe false (foldl1 $ binApp orOp) (nonEmpty andExprs)
 where
  false = ConE $ mkName "False"
  orOp = VarE $ mkName "||"
  andExprs = mapMaybe (mkAndExpr mkSelector fieldMap operands) uniqueDefs

mkAndExpr :: (HaskellName -> Name) -> FieldMap -> (Name, Name) -> UniqueDef -> Maybe Exp
mkAndExpr mkSelector fieldMap operands UniqueDef{..} =
  foldl1 (binApp andOp) <$> nonEmpty comparisons
 where
  andOp = VarE $ mkName "&&"
  fields = map fst uniqueFields
  nonForeignFields = mapMaybe (uncurry comparisonType . (id &&& (fieldMap Map.!))) fields
  comparisons = map (mkComparison mkSelector operands) nonForeignFields

data ComparisonType
  = PlainEquality HaskellName
  | OnlyNonNull HaskellName

comparisonType :: HaskellName -> (ReferenceDef, IsNullable) -> Maybe ComparisonType
comparisonType name pair =
  case pair of
    (ForeignRef{}, _) -> Nothing
    (_, Nullable{}) -> pure (OnlyNonNull name)
    (_, NotNullable) -> pure (PlainEquality name)

mkComparison :: (HaskellName -> Name) -> (Name, Name) -> ComparisonType -> Exp
mkComparison mkSelector operands (PlainEquality name) = mkEqComparison operands (mkSelector name)
mkComparison mkSelector operands (OnlyNonNull name) = mkNonNullEqComparison operands (mkSelector name)

mkEqComparison :: (Name, Name) -> Name -> Exp
mkEqComparison (lhs, rhs) selector =
  binApp
    (VarE $ mkName "==")
    (VarE selector `AppE` VarE lhs)
    (VarE selector `AppE` VarE rhs)

mkNonNullEqComparison :: (Name, Name) -> Name -> Exp
mkNonNullEqComparison (lhs, rhs) selector =
  VarE (mkName "maybe")
    `AppE` ConE (mkName "False")
    `AppE` VarE (mkName "id")
    `AppE` ParensE
      (binApp
        (VarE $ mkName "<*>")
        (binApp
          (VarE $ mkName "<$>")
          (VarE $ mkName "==")
          (VarE selector `AppE` VarE lhs))
        (VarE selector `AppE` VarE rhs))

binApp :: Exp -> Exp -> Exp -> Exp
binApp f x y = UInfixE x f y
