{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RecordWildCards #-}
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
import Data.Proxy (Proxy(..))
import Data.Text (Text, pack)
import Data.Time.Calendar
import Data.Time.Clock
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
import Data.Graph.HGraph.TH

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
    where isBadChar x = x == '\NUL' || x == '\\' -- These make postgres vomit

_entityKey :: Lens' (Entity a) (Key a)
_entityKey pure' (Entity i e) = (\i' -> Entity i' e) <$> pure' i

share [mkPersist sqlSettings { mpsGenerateLenses = True },  mkMigrate "testMigrate"] [persistUpperCase|
  District
    name Text
    createdAt UTCTime
    deriving Show Eq Generic
  School
    name Text
    createdAt UTCTime
    districtId DistrictId Maybe
    deriving Show Eq Generic
  Teacher
    name Text
    createdAt UTCTime
    schoolId SchoolId
    deriving Show Eq Generic
  Student
    name Text
    createdAt UTCTime
    teacherId TeacherId
    deriving Show Eq Generic
  MultiPointer
    name
    teacherId TeacherId
    schoolId  SchoolId
    deriving Show Eq Generic
|]
instance Arbitrary District where
  arbitrary = District <$> arbitrary <*> arbitrary
instance Arbitrary School where
  arbitrary = School <$> arbitrary <*> arbitrary <*> arbitrary
instance Arbitrary Teacher where
  arbitrary = Teacher <$> arbitrary <*> arbitrary <*> arbitrary
instance Arbitrary Student where
  arbitrary = Student <$> arbitrary <*> arbitrary <*> arbitrary
instance Arbitrary MultiPointer where
  arbitrary = MultiPointer <$> arbitrary <*> arbitrary
instance Arbitrary Day where
  arbitrary = ModifiedJulianDay <$> arbitrary
instance Arbitrary DiffTime where
  arbitrary = secondsToDiffTime <$> arbitrary
instance Arbitrary UTCTime where
  arbitrary = UTCTime <$> arbitrary <*> arbitrary

declareBases [''MultiPointer, ''District, ''School, ''Student, ''Teacher, ''Text, ''UTCTime]

instance Student `PointsAt` Entity Teacher
instance Teacher `PointsAt` Entity School
instance School `PointsAt` Maybe (Entity District)
instance MultiPointer `PointsAt` Entity Teacher
instance MultiPointer `PointsAt` Entity School

type M = ReaderT SqlBackend (LoggingT (ResourceT IO))

studentIsInDistrict :: Entity Student -> Entity Teacher -> Entity School -> Entity District -> Bool
studentIsInDistrict
  (Entity _ Student{ .. })
  (Entity teacherId Teacher{ .. })
  (Entity schoolId School{ _schoolDistrictId })
  (Entity districtId _) =
    _studentTeacherId == teacherId &&
    _teacherSchoolId == schoolId &&
    _schoolDistrictId == Just districtId &&
    _studentName /= _teacherName

arbitrary' :: (Arbitrary a) => M a
arbitrary' = liftIO (generate arbitrary)

main :: IO ()
main = do
  now <- getCurrentTime
  runConn $ runMigrationUnsafe testMigrate
  hspec $
    describe "" $ do
      it "we can test our function the old-fashioned way" $ db $ do
        district@(Entity districtId _) <- insertEntity $ District "districtName" now
        school1@(Entity schoolId1 _) <- insertEntity $ School "school1" now (Just districtId)
        school2@(Entity schoolId2 _) <- insertEntity $ School "school2" now Nothing
        teacher1@(Entity teacherId1 _) <- insertEntity $ Teacher "teacher1" now schoolId1
        teacher2@(Entity teacherId2 _) <- insertEntity $ Teacher "teacher2" now schoolId2
        student@(Entity studentId _) <- insertEntity $ Student "student1" now teacherId1
        liftIO $ studentIsInDistrict student teacher1 school1 district `shouldBe` True
      it "but this is tedious and, consequently, error prone" $ db $ do
        district@(Entity districtId _) <- insertEntity $ District "districtName" now
        school1@(Entity schoolId1 _) <- insertEntity $ School "school1" now (Just districtId)
        school2@(Entity schoolId2 _) <- insertEntity $ School "school2" now Nothing
        teacher1@(Entity teacherId1 _) <- insertEntity $ Teacher "teacher1" now schoolId2
        teacher2@(Entity teacherId2 _) <- insertEntity $ Teacher "teacher2" now schoolId2
        student@(Entity studentId _) <- insertEntity $ Student "student1" now teacherId1
        liftIO $ studentIsInDistrict student teacher1 school1 district `shouldBe` True
      it "furthermore, it's not obvious which properties of the item we care about" $ db $ do
        district@(Entity districtId _) <- insertEntity $ District "districtName" now
        school1@(Entity schoolId1 _) <- insertEntity $ School "school1" now (Just districtId)
        school2@(Entity schoolId2 _) <- insertEntity $ School "school2" now Nothing
        teacher1@(Entity teacherId1 _) <- insertEntity $ Teacher "1" now schoolId1
        teacher2@(Entity teacherId2 _) <- insertEntity $ Teacher "teacher2" now schoolId2
        student@(Entity studentId _) <- insertEntity $ Student "1" now teacherId1
        liftIO $ studentIsInDistrict student teacher1 school1 district `shouldBe` True
      it "using 'Arbitrary` can help, especially with that last problem. But now we have to set each FK by hand" $ db $ do
        district@(Entity districtId _) <- insertEntity =<< arbitrary'
        school1@(Entity schoolId1 _) <- insertEntity . set schoolDistrictId (Just districtId) =<< arbitrary'
        school2@(Entity (schoolId2 :: Key School) _) <- insertEntity =<< arbitrary'
        teacher1@(Entity teacherId1 _) <- insertEntity . set teacherSchoolId schoolId1 . set teacherName "Foo" =<< arbitrary'
        teacher2@(Entity (teacherId2 :: Key Teacher) _) <- insertEntity =<< arbitrary'
        student@(Entity studentId _) <- insertEntity . set studentTeacherId teacherId1 . set studentName "Bar" =<< arbitrary'
        liftIO $ studentIsInDistrict student teacher1 school1 district `shouldBe` True
      it "enter HGraph" $ db $ do
        arbGraph <- unRawGraph <$> arbitrary'
        (st :< te :< sc :< Always di :< Nil) <-
          insertGraph arbGraph :: M (Line '[Entity Student, Entity Teacher, Entity School, Always (Entity District)])
        pure ()
        -- liftIO $ studentIsInDistrict st te sc di `shouldBe` True
      it "And we can set nested properties we care about" $ db $ do
        arbGraph <- unRawGraph <$> arbitrary'
        let arbGraph' =
              arbGraph
                & pluck (Proxy :: Proxy (Entity Teacher)) . teacherName .~ "Foo"
                & pluck (Proxy :: Proxy (Entity Student)) . studentName .~ "Bar"
        (st :< te :< sc :< Always di :< Nil) <-
          insertGraph arbGraph' :: M (Line '[Entity Student, Entity Teacher, Entity School, Always (Entity District)])
        pure ()
        -- liftIO $ studentIsInDistrict st te sc di `shouldBe` True
      it "we can also omit some entities and get sensible defaulting" $ db $ do
        arbGraph <- unRawGraph <$> arbitrary'
        (st :< te :< sc :< Nil) <-
          insertGraph arbGraph :: M (Line '[Entity Student, Entity Teacher, Entity School])
        pure ()
        -- liftIO $ sc ^. _entityVal . schoolDistrictId  `shouldBe` Nothing
      it "but if we omit entities that are required, we get a type error" $ db $ do
        -- arbGraph <- unRawGraph <$> arbitrary'
        -- (st :< te :< Nil) <-
        --   insertGraph arbGraph :: M (Line '[Entity Student, Entity Teacher])
        pure ()
      it "finally, we can do much more complicated directed graphs, if we need to" $ db $ do
        arbGraph <- arbitrary'
          ::
            M (
              HGraph
                '[ '("Student1", '["Teacher1"], Entity Student)
                 , '("Student2", '["Teacher2"], Entity Student)
                 , '("Multi", '["Teacher1", "School"], Entity MultiPointer)
                 , '("Teacher1", '["School"], Entity Teacher)
                 , '("Teacher2", '["School"], Entity Teacher)
                 , '("School", '["District"], Entity School)
                 , '("District", '[], Maybe (Entity District))
                 ]
              )
        pure ()
      --   liftIO $ print arbGraph
