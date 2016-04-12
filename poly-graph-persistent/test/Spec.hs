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

import Control.Lens hiding ((:<), _head, _tail)
import Control.Monad (void)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger (LoggingT(..))
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.Resource (ResourceT, runResourceT, MonadBaseControl)
import qualified Data.ByteString.Char8 as B8
import Data.Maybe
import Data.Proxy (Proxy(..))
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

instance (Arbitrary a) => Arbitrary (Always a) where
  arbitrary = pure <$> arbitrary
instance Arbitrary (Never a) where
  arbitrary = pure Never

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
  Foo
    name Text
    studentId StudentId Maybe
    teacherId TeacherId Maybe
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
instance Arbitrary Foo where
  arbitrary = Foo "foo" <$> arbitrary <*> arbitrary

-- We ought to be able to provide a generic instance like
-- @instance (a `PointsAt` Maybe b) => a `PointsAt` b where a `pointsAt` b = a `pointsAt` Just b@
-- However, if we do, any graphs with a missing instance match this instance and then fail via
-- a context reduction stack overflow which is pretty ugly.

instance ToBase SelfRef where
  type HasBase SelfRef = 'True
  type Base SelfRef = SelfRef
  base = id
instance ToBase District where
  type HasBase District = 'True
  type Base District = District
  base = id
-- instance ToBase School where
--   type HasBase School = 'True
--   type Base School = School
--   base = id
-- instance ToBase Student where
--   type HasBase Student = 'True
--   type Base Student = Student
--   base = id
-- instance ToBase Teacher where
--   type HasBase Teacher = 'True
--   type Base Teacher = Teacher
--   base = id
-- instance ToBase Foo where
--   type HasBase Foo = 'True
--   type Base Foo = Foo
--   base = id

instance SelfRef `PointsAt` Entity SelfRef
instance SelfRef `PointsAt` Maybe (Entity SelfRef)
instance Student `PointsAt` Entity Teacher
instance Teacher `PointsAt` Entity School
instance School `PointsAt` Maybe (Entity District)
instance Foo `PointsAt` Entity Student
instance Foo `PointsAt` Entity Teacher

_entityKey :: Lens' (Entity a) (Key a)
_entityKey pure' (Entity i e) = (\i' -> Entity i' e) <$> pure' i

type M = ReaderT SqlBackend (LoggingT (ResourceT IO))
main :: IO ()
main = do
  runConn $ runMigrationUnsafe testMigrate
  hspec $
    describe "poly-graph-persistent" $ do
      it "works with plucked lenses" $ db $ do
        graph <-
          unRawGraph <$> liftIO (generate arbitrary)
            :: M (Line '[Student, Teacher, School])
        let graph' = graph & pluck (Proxy :: Proxy School) . schoolName .~ "Hello"
        liftIO $ print graph'
      -- it "doesn't type check with a dangling (non-`Maybe`) key" $ db $ do
      --   graph <- liftIO (generate arbitrary) :: M (HGraph '[ '(Teacher, "Teacher", '[]) ])
      --   liftIO $ print graph
      -- it "doesn't type check with a repeated name" $ db $ do
      --   graph <-
      --     liftIO (generate arbitrary)
      --     :: M (HGraph '[ '(Teacher, "Teacher", '["Teacher"]), '(Student, "Teacher", '[]) ])
      --   liftIO $ print graph
      it "generates arbitrary entities" $ db $ do
        graph <-
          liftIO (generate arbitrary)
            :: M (Line '[Entity Student, Entity Teacher, Entity School, Always (Entity District)])
        liftIO $ print graph
      it "defaults only missing keys to nothing" $ db $ do
        arbGraph <- unRawGraph <$> liftIO (generate arbitrary)
        entGraph <-
          insertGraph arbGraph
          :: M (
               HGraph
                '[ '(Entity Foo, "F", '["S"])
                 , '(Entity Student, "S", '["T"])
                 , '(Entity Teacher, "T", '["Sc"])
                 , '(Entity School, "Sc", '[])
                 ]
               )
        liftIO $ (entGraph ^. _head . _entityVal . fooTeacherId) `shouldBe` Nothing
        liftIO $ (entGraph ^. _head . _entityVal . fooStudentId) `shouldBe` (Just $ entGraph ^. _tail . _head . _entityKey)
      it "defaults `Maybe` keys to `Nothing` during `Arbitrary` creation when they're at the end of the graph" $ db $ do
        arbGraph <- liftIO (generate arbitrary) :: M (Line '[Maybe (Entity SelfRef)])
        liftIO $ (arbGraph ^? _head . _Just . _entityVal . selfRefSelfRefId . _Just) `shouldBe` Nothing
      it "defaults `Maybe` keys to `Nothing` during insertion when they're at the end of the graph" $ db $ do
        entGraph <- insertGraph . unRawGraph =<< liftIO (generate arbitrary) :: M (Line '[Maybe (Entity SelfRef)])
        liftIO $ (entGraph ^? _head . _Just . _entityVal . selfRefSelfRefId . _Just) `shouldBe` Nothing
      it "defaults `Maybe` keys to `Nothing` during `Arbitrary` creation when they're in the middle of the graph" $ db $ do
        arbGraph <-
          liftIO (generate arbitrary)
          :: M (HGraph '[ '(Always (Entity SelfRef), 1, '[]), '(Maybe (Entity SelfRef), 2, '[]) ])
        liftIO $ (arbGraph ^? _head . _Always . _entityVal . selfRefSelfRefId . _Just) `shouldBe` Nothing
      it "defaults `Maybe` keys to `Nothing` during insertion when they're in the middle of the graph" $ db $ do
        entGraph <-
          insertGraph . unRawGraph =<< liftIO (generate arbitrary)
          :: M (HGraph '[ '(Always (Entity SelfRef), 1, '[]), '(Maybe (Entity SelfRef), 2, '[]) ])
        liftIO $ (entGraph ^? _head . _Always . _entityVal . selfRefSelfRefId . _Just) `shouldBe` Nothing
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
        graph' <-
          insertGraph graph
            :: M (
                 HGraph
                   '[ '(Entity SelfRef, "Plain1", '["Plain2"])
                    , '(Entity SelfRef, "Plain2", '["Never"])
                    , '(Never (Entity SelfRef), "Never", '[])
                    ]
                 )
        liftIO $
          (graph' ^. pluck (Proxy :: Proxy "Plain1") . _entityVal . selfRefSelfRefId) `shouldBe`
          (Just $ graph' ^. pluck (Proxy :: Proxy "Plain2") . _entityKey)
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
        (st :< te :< sc :< Always di :< Nil) <-
          insertGraph graph
            :: M (
                 HGraph
                   '[ Ty (Entity Student) '[Entity Teacher]
                    , Ty (Entity Teacher) '[Entity School]
                    , Ty (Entity School) '[Always (Entity District)]
                    , Ty (Always (Entity District)) '[]
                    ]
                 )

        let manualTree = (Entity stId stB, Entity teId teB, Entity scId scB, Entity diId diB)
        let autoTree = (st, te, sc, di)
        liftIO $ autoTree `shouldBe` manualTree
        liftIO $ print autoTree
