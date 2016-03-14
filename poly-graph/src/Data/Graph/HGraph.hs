{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- Pattern synonyms and exhaustivity checking don't work well together
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module Data.Graph.HGraph
  ( module Data.Graph.HGraph
  , X.HGraph(Nil)
  ) where

import Data.Tagged (Tagged(..), retag)
import Generics.Eot (Void, fromEot, toEot, Eot, HasEot)
import GHC.TypeLits

import Data.Graph.HGraph.Internal as X

infixr 5 `Link`
class a `Link` b where
  infixr 5 `link`
  link :: a -> b -> a
  default link :: (HasEot a, (Eot a) `GLink` b) => a -> b -> a
  link a b = fromEot $ toEot a `gLink` b

class a `GLink` b where
  infixr 5 `gLink`
  gLink :: a -> b -> a
instance (b `GLink` c) => (a, b) `GLink` c where
  (a, b) `gLink` c = (a, b `gLink` c)
instance (a `GLink` c, b `GLink` c) => Either a b `GLink` c where
  Left a `gLink` b = Left $ a `gLink` b
  Right a `gLink` b = Right $ a `gLink` b
instance GLink Void a where
  gLink _ _ = error "impossible"

infixr 5 :::
pattern a ::: b <- Tagged a `Cons` b

class a `LinkR` b where
  linkR :: a -> b -> a
-- | End of graph
instance {-# OVERLAPPING #-} Tagged '(i, '[]) a `LinkR` HGraph '[] where
  linkR = const
-- | Points at nothing
instance Tagged '(i, '[]) a `LinkR` (HGraph b) where
  linkR = const
-- | Points at wrong thing
instance (Tagged '(i, j ': js) a `LinkR` HGraph c) => Tagged '(i, j ': js) a `LinkR` (HGraph ('(b, k, ls) ': c)) where
  a `linkR` Cons _ c = a `linkR` c
-- | Adjacent
instance {-# OVERLAPPING #-}
  (a `Link` b, Tagged '(i, js) a `LinkR` (HGraph ('(b, j, ks) ': c))) =>
  Tagged '(i, j ': js) a `LinkR` (HGraph ('(b, j, ks) ': c)) where
  a `linkR` Cons b c = retag $ a' `linkR` r
    where
      r :: HGraph ('(b, j, ks) ': c)
      r = Cons b c
      a' :: Tagged '(i, js) a
      a' = retag $ (`link` unTagged b) <$> a

infixr 5 ~>
(~>) :: ((Tagged '(i, is) a) `LinkR` HGraph b) => a -> HGraph b -> HGraph ('(a, i, is) ': b)
a ~> b = (Tagged a `linkR` b) `Cons` b

infixr 5 :<:
data a :<: b = a :<: b
type Tree a = HGraph (Tree' 0 1 a)
infixr 5 :++:
type family x :++: y where
  '[] :++: y = y
  (a ': b) :++: y = a ': b :++: y

type BranchSize = 100
type family Tree' n x a where
  Tree' n x (b :<: (c, d)) =
    '(b, n, '[n + 1 * BranchSize ^ x, n + 2 * BranchSize ^ x]) ':
      (Tree' (n + 1 * BranchSize ^ x) (x + 1) c) :++:
      (Tree' (n + 2 * BranchSize ^ x) (x + 1) d)
  Tree' n x (b :<: c :<: d) = '(b, n, '[n + 1]) ': Tree' (n + 1) x (c :<: d)
  Tree' n x (b :<: c) = '(b, n, '[n + 1]) ': '(c, n + 1, '[]) ': '[]
  Tree' n x b = '(b, n, '[]) ': '[]

class TreeConv a b | a -> b where
  tree :: a -> b
-- | Points at nothing
instance TreeConv (HGraph ('(a, n, '[]) ': x)) a where
  tree (a ::: Nil) = a
-- | Branch
instance
  ( TreeConv (HGraph ('(b, m, x) ': z)) i
  , TreeConv (HGraph ('(c, o, y) ': z)) j
  ) =>
  TreeConv (HGraph ('(a, n, '[m, o]) ': '(b, m, x) ': '(c, o, y) ': z)) (a :<: (i, j)) where
  tree (a ::: b `Cons` c `Cons` x) = a :<: (tree $ b `Cons` x, tree $ c `Cons` x)
-- | Points at wrong thing
instance {-# OVERLAPPABLE #-}
  ( TreeConv (HGraph ('(a, n, '[m]) ': y)) i
  , TreeConv (HGraph ('(b, o, x) ': y)) j
  ) =>
  TreeConv (HGraph ('(a, n, '[m]) ': '(b, o, x) ': y)) (i :<: j) where
  tree (a `Cons` b `Cons` c) = tree (a `Cons` c) :<: tree (b `Cons` c)
-- | Adjacent
instance
  ( TreeConv (HGraph ('(b, m, x) ': y)) j
  ) =>
  TreeConv (HGraph ('(a, n, '[m]) ': '(b, m, x) ': y)) (a :<: j) where
  tree (a ::: b) = a :<: tree b
