{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

import Test.Hspec

import Control.Lens
import Control.Monad (void)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger (LoggingT(..))
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.Resource (ResourceT, runResourceT, MonadBaseControl)
import Data.DeriveTH (derive, makeArbitrary)
import Data.Text (Text, pack)
import Database.Persist
import Database.Persist.Sql
import Database.Persist.Sqlite (withSqlitePool)
import Database.Persist.TH
import System.Log.FastLogger (fromLogStr)
import Test.QuickCheck.Arbitrary (Arbitrary(..))
import Test.QuickCheck.Gen (generate)

import Data.Graph.HGraph
import Data.Graph.HGraph.Persistent

db :: SqlPersistT (LoggingT (ResourceT IO)) a -> IO ()
db actions = runResourceT $ runConn $ actions >> transactionUndo

runConn :: (MonadIO m, MonadBaseControl IO m) => SqlPersistT (LoggingT m) t -> m ()
runConn f =
  void . flip runLoggingT (\_ _ _ s -> print $ fromLogStr s) $
  withSqlitePool "test/testdb.sqlite3" 1 $
  runSqlPool f

instance Arbitrary Text where
  arbitrary = pack . filter (not . isBadChar) <$> arbitrary
    where isBadChar x = x == '\NUL' || x == '\\' -- Make postgres vomit
instance (ToBackendKey SqlBackend a) => Arbitrary (Key a) where
  arbitrary = toSqlKey <$> arbitrary
instance (ToBackendKey SqlBackend a, Arbitrary a) => Arbitrary (Entity a) where
  arbitrary = Entity <$> arbitrary <*> arbitrary
-- | No-op instance for use with `insertGraph`
instance {-# OVERLAPPABLE #-} (Entity a ~~> Entity b) => a ~~> b where
  a ~~> _ = a
instance {-# OVERLAPPABLE #-} (a ~~> Entity b) => Entity a ~~> Entity b where
  Entity id' a ~~> b = Entity id' $ a ~~> b

share [mkPersist sqlSettings { mpsGenerateLenses = False },  mkMigrate "testMigrate"] [persistUpperCase|
  District
    name Text
  School
    name Text
    districtId DistrictId Maybe
    deriving Show
  Teacher
    name Text
    schoolId SchoolId
    mentorId TeacherId
    deriving Show
  Student
    name Text
    teacherId TeacherId
    deriving Show
  Lectern
    teacherId TeacherId Maybe -- Some lecterns are unowned
    deriving Show
|]
$(derive makeArbitrary ''Teacher)
$(derive makeArbitrary ''Student)
$(derive makeArbitrary ''School)

instance Student ~~> Entity Teacher where
  s ~~> Entity tId _ = s { studentTeacherId = tId }
instance Teacher ~~> Entity School where
  t ~~> Entity sId _ = t { teacherSchoolId = sId }
instance Teacher ~~> Entity Teacher where
  t ~~> Entity tId _ = t { teacherMentorId = tId }

-- entityVal :: Lens' (Entity a) a
-- entityVal = lens getter setter
--   where
--     getter (Entity _ v) = v
--     setter (Entity k _) v = Entity k v

-- entityKey :: Lens (Entity a) (Key a)
-- entityKey = lens getter setter
--   where
--     getter (Entity k _) = k
--     setter (Entity _ v) k = Entity k v

type M = ReaderT SqlBackend (LoggingT (ResourceT IO))
main :: IO ()
main = do
  runConn $ runMigrationUnsafe testMigrate
  hspec $
    describe "persistent" $ do
      it "foo" $ db $ do
        (t :: Teacher) <- liftIO $ generate arbitrary
        tId <- insert t
        insert $ Student "bar" tId
      it "bar" $ db $ do
        g <- liftIO $ generate arbitrary :: M (Entity Student :~>: Entity Teacher)
        insertEntityGraph g :: M ()
      it "baz" $ db $ do
        g <- liftIO $ generate arbitrary :: M (Student :~>: Teacher)
        g' <- insertGraph g :: M (Entity Student :~>: Entity Teacher)
        liftIO $ print g'
      it "qux" $ db $ do
        g <- liftIO $ generate arbitrary :: M (FromMany (Teacher :~>: ToMany (FromTo Teacher)) :~>: School)
        g' <- liftIO $ generate arbitrary :: M (FromMany (Entity Teacher :~>: ToMany (FromTo (Entity Teacher))) :~>: Entity School)
        liftIO $ print g'
