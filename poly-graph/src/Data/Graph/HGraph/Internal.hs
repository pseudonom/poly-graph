{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | You should try to avoid using this module.
-- It has the raw @PointsTo@ and consequently allows you to construct @:~>:@
-- which aren't actually linked.
module Data.Graph.HGraph.Internal where

import Data.Monoid ((<>))
import GHC.Generics (Generic)
import Test.QuickCheck.Arbitrary (Arbitrary(..))

data Node (i :: k) (is :: [k]) a = Node { unNode :: a } deriving (Eq, Show, Functor, Generic)

retag :: Node i is a -> Node j js a
retag (Node a) = Node a


data IsDuplicateName a
  = UniqueName
  | DuplicateName a

type family Member (a :: k) (as :: [(k, [k], *)]) :: IsDuplicateName k where
  Member a '[] = 'UniqueName
  Member name ('(name, js, b) ': as) = 'DuplicateName name
  Member a (b ': as) = Member a as

infixr 5 `Cons`
data HGraph y where
  Cons :: ((i `Member` b) ~ 'UniqueName) => Node i is a -> HGraph b -> HGraph ('(i, is, a) ': b)
  Nil :: HGraph '[]


type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t
type Lens' s a = Lens s s a a

-- | Please don't use these lenses to edit the FK fields
_head :: Lens' (HGraph ('(i, is, a) ': b)) a
_head pure' (Node a `Cons` b) = (`Cons` b)  . Node <$> pure' a

-- | Please don't use these lenses to edit the FK fields
_tail :: Lens' (HGraph (a ': b)) (HGraph b)
_tail pure' (a `Cons` b) = (a `Cons`) <$> pure' b


instance (Arbitrary a) => Arbitrary (Node i is a) where
  arbitrary = Node <$> arbitrary

instance (Show x, Show (HGraph xs)) => Show (HGraph ('(i, is, x) ': xs)) where
  show (Cons x y) = "Cons (" <> show x <> ") (" <> show y <> ")"
instance Show (HGraph '[]) where
  show Nil = "Nil"
instance (Eq x, Eq (HGraph xs)) => Eq (HGraph ('(i, is, x) ': xs)) where
  (Cons x1 xs1) == (Cons x2 xs2) = x1 == x2 && xs1 == xs2
instance Eq (HGraph '[]) where
  Nil == Nil = True
