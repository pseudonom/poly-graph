{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

import Test.Hspec

import Control.Lens hiding ((:<), _head)
import Control.Monad (void)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger (LoggingT(..))
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.Resource (ResourceT, runResourceT, MonadBaseControl)
import qualified Data.ByteString.Char8 as B8
import Data.Text (Text, pack)
import Data.Type.Equality (type (==))
import Database.Persist
import Database.Persist.Sql
import Database.Persist.Sqlite (withSqlitePool)
import Database.Persist.TH
import GHC.Generics (Generic)
import System.Log.FastLogger (fromLogStr)
import Test.QuickCheck.Arbitrary (Arbitrary(..))
import Test.QuickCheck.Gen (generate)

import Data.Graph.HGraph
import Data.Graph.HGraph.Instances ()
import Data.Graph.HGraph.Persistent

db :: SqlPersistT (LoggingT (ResourceT IO)) a -> IO ()
db actions = runResourceT $ runConn $ actions >> transactionUndo

runConn :: (MonadIO m, MonadBaseControl IO m) => SqlPersistT (LoggingT m) t -> m ()
runConn f =
  void . flip runLoggingT (\_ _ _ s -> B8.putStrLn $ fromLogStr s) $
  withSqlitePool "test/testdb.sqlite3" 1 $
  runSqlPool f

instance Arbitrary Text where
  arbitrary = pack . filter (not . isBadChar) <$> arbitrary
    where isBadChar x = x == '\NUL' || x == '\\' -- Make postgres vomit

share [mkPersist sqlSettings { mpsGenerateLenses = True },  mkMigrate "testMigrate"] [persistUpperCase|
  SelfRef
    name Text
    selfRefId SelfRefId Maybe
    deriving Show Eq Generic
  District
    name Text
    deriving Show Eq Generic
  School
    name Text
    districtId DistrictId Maybe
    deriving Show Eq Generic
  Teacher
    name Text
    schoolId SchoolId
    deriving Show Eq Generic
  Student
    name Text
    teacherId TeacherId
    deriving Show Eq Generic
|]
instance Arbitrary District where
  arbitrary = pure $ District "foo"
instance Arbitrary School where
  arbitrary = School "bar" <$> arbitrary
instance Arbitrary Teacher where
  arbitrary = Teacher "baz" <$> arbitrary
instance Arbitrary Student where
  arbitrary = Student "qux" <$> arbitrary
instance Arbitrary SelfRef where
  arbitrary = SelfRef "self" <$> arbitrary

-- We ought to be able to provide a generic instance like
-- @instance (a `PointsAt` Maybe b) => a `PointsAt` b where a `pointsAt` b = a `pointsAt` Just b@
-- However, if we do, any graphs with a missing instance match this instance and then fail via
-- a context reduction stack overflow which is pretty ugly.
instance SelfRef `PointsAt` (Entity SelfRef)
instance SelfRef `PointsAt` (Maybe (Entity SelfRef))
instance Student `PointsAt` (Entity Teacher)
instance Teacher `PointsAt` (Entity School)
instance School `PointsAt` (Maybe (Entity District))

type M = ReaderT SqlBackend (LoggingT (ResourceT IO))
main :: IO ()
main = do
  runConn $ runMigrationUnsafe testMigrate
  hspec $
    describe "poly-graph-persistent" $ do
      it "allows defaults maybe keys to nothing" $ db $ do
        graph <-
          liftIO (generate arbitrary)
            :: M (HGraph '[ '(Entity SelfRef, "Plain", '[]) ])
        liftIO $ (view selfRefSelfRefId . entityVal . view _head $ graph) `shouldBe` Nothing
      it "works with Maybe key to plain" $ db $ do
        graph <-
          unRawGraph <$> liftIO (generate arbitrary)
            :: M (
                 HGraph
                   '[ '(SelfRef, "Plain1", '["Plain2"])
                    , '(SelfRef, "Plain2", '["Never"])
                    , '(Never SelfRef, "Never", '[])
                    ]
                 )
        liftIO $ print graph
        graph' <-
          insertGraph graph
            :: M (
                 HGraph
                   '[ '(Entity SelfRef, "Plain1", '["Plain2"])
                    , '(Entity SelfRef, "Plain2", '["Never"])
                    , '(Never (Entity SelfRef), "Never", '[])
                    ]
                 )
        liftIO $ print graph'
      it "works with a variety of `Maybe`, `Always`, `Never` combinations" $ db $ do
        graph <-
          unRawGraph <$> liftIO (generate arbitrary)
            :: M (
                 HGraph
                   '[ '(SelfRef, "Plain1", '["Maybe1", "Always1", "Never1", "Plain2"])
                    , '(Maybe SelfRef, "Maybe1", '["Always1", "Never1", "Plain2", "Maybe2"])
                    , '(Always SelfRef, "Always1", '["Never1", "Plain2", "Maybe2", "Always2"])
                    , '(Never SelfRef, "Never1", '["Plain2", "Maybe2", "Always2", "Never2"])
                    , '(SelfRef, "Plain2", '["Never2"])
                    , '(Maybe SelfRef, "Maybe2", '["Never2"])
                    , '(Always SelfRef, "Always2", '["Never2"])
                    , '(Never SelfRef, "Never2", '[])
                    ]
                 )
        liftIO $ print graph
        graph' <-
          insertGraph graph
            :: M (
                 HGraph
                   '[ '(Entity SelfRef, "Plain1", '["Maybe1", "Always1", "Never1", "Plain2"])
                    , '(Maybe (Entity SelfRef), "Maybe1", '["Always1", "Never1", "Plain2", "Maybe2"])
                    , '(Always (Entity SelfRef), "Always1", '["Never1", "Plain2", "Maybe2", "Always2"])
                    , '(Never (Entity SelfRef), "Never1", '["Plain2", "Maybe2", "Always2", "Never2"])
                    , '(Entity SelfRef, "Plain2", '["Never2"])
                    , '(Maybe (Entity SelfRef), "Maybe2", '["Never2"])
                    , '(Always (Entity SelfRef), "Always2", '["Never2"])
                    , '(Never (Entity SelfRef), "Never2", '[])
                    ]
                 )
        liftIO $ print graph'


      it "Manual creation and insertion should produce the same results as automatic creation and insertion" $ db $ do
        void . insert $ District "bump id to prove we're doing something mildly interesting"

        diB <- liftIO $ generate arbitrary
        diId <- insert diB
        scB <- fmap (set schoolDistrictId (Just diId)) . liftIO $ generate arbitrary
        scId <- insert scB
        teB <- fmap (set teacherSchoolId scId) . liftIO $ generate arbitrary
        teId <- insert teB
        stB <- fmap (set studentTeacherId teId) . liftIO $ generate arbitrary
        stId <- insert stB

        transactionUndo
        void . insert $ District "bump id to prove we're doing something mildly interesting"

        graph <-
          unRawGraph <$> liftIO (generate arbitrary)
            :: M (Tree (Student :< Teacher :< School :< Always District))
        (tree -> st :< te :< sc :< Always di) <-
          insertGraph graph
            :: M (Tree (Entity Student :< Entity Teacher :< Entity School :< Always (Entity District)))

        let manualTree = (Entity stId stB, Entity teId teB, Entity scId scB, Entity diId diB)
        let autoTree = (st, te, sc, di)
        liftIO $ autoTree `shouldBe` manualTree
        liftIO $ print autoTree
