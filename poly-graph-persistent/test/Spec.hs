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
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

import Test.Hspec

import Control.Lens
import Control.Monad (void)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger (LoggingT(..))
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.Resource (ResourceT, runResourceT, MonadBaseControl)
import qualified Data.ByteString.Char8 as B8
import Data.Text (Text, pack)
import Database.Persist
import Database.Persist.Sql
import Database.Persist.Sqlite (withSqlitePool)
import Database.Persist.TH
import System.Log.FastLogger (fromLogStr)
import Test.QuickCheck.Arbitrary (Arbitrary(..))
import Test.QuickCheck.Gen (generate)

import Data.Graph.HGraph
import Data.Graph.HGraph.Arbitrary ()
import Data.Graph.HGraph.Persistent

_entityKey :: Lens' (Entity a) (Key a)
_entityKey = lens getter setter
  where
    getter (Entity k _) = k
    setter (Entity _ v) k = Entity k v

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
instance (ToBackendKey SqlBackend a) => Arbitrary (Key a) where
  arbitrary = toSqlKey <$> arbitrary
instance (ToBackendKey SqlBackend a, Arbitrary a) => Arbitrary (Entity a) where
  arbitrary = Entity <$> arbitrary <*> arbitrary
instance {-# OVERLAPPABLE #-} (a `Link` Entity b) => Entity a `Link` Entity b where
  Entity id' a `link` b = Entity id' $ a `link` b
-- | No-op instances for use with `insertGraph`
instance {-# OVERLAPPABLE #-} (Entity a `Link` Entity b) => a `Link` b where
  a `link` _ = a
instance {-# OVERLAPPABLE #-} (a `Link` Maybe (Entity b)) => a `Link` Maybe b where
  a `link` _ = a

share [mkPersist sqlSettings { mpsGenerateLenses = True },  mkMigrate "testMigrate"] [persistUpperCase|
  District
    name Text
    deriving Show Eq
  School
    name Text
    districtId DistrictId Maybe
    deriving Show Eq
  Teacher
    name Text
    schoolId SchoolId
    deriving Show Eq
  Student
    name Text
    teacherId TeacherId
    deriving Show Eq
  Lectern
    teacherId TeacherId Maybe -- Some lecterns are unowned
    deriving Show Eq
|]
instance Arbitrary District where
  arbitrary = pure $ District "foo"
instance Arbitrary School where
  arbitrary = School "bar" <$> arbitrary
instance Arbitrary Teacher where
  arbitrary = Teacher "baz" <$> arbitrary
instance Arbitrary Student where
  arbitrary = Student "qux" <$> arbitrary
instance Arbitrary Lectern where
  arbitrary = Lectern <$> arbitrary

instance Student `Link` Entity Teacher where
  s `link` Entity tId _ = s & studentTeacherId .~ tId
instance Teacher `Link` Entity School where
  t `link` Entity sId _ = t & teacherSchoolId .~ sId
instance School `Link` Maybe (Entity District) where
  s `link` d = s & schoolDistrictId .~ d ^? _Just . _entityKey

type M = ReaderT SqlBackend (LoggingT (ResourceT IO))
main :: IO ()
main = do
  runConn $ runMigrationUnsafe testMigrate
  hspec $
    describe "persistent" $ do
      it "foo" $ db $ do
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

        (tree -> st :<: te :<: sc :<: Always di) <-
          insertGraph =<< liftIO (generate arbitrary)
          :: M (Tree (Entity Student :<: Entity Teacher :<: Entity School :<: Always (Entity District)))

        let manualTree = (Entity stId stB, Entity teId teB, Entity scId scB, Entity diId diB)
        let autoTree = (st, te, sc, di)
        liftIO $ manualTree `shouldBe` autoTree
        liftIO $ print autoTree
