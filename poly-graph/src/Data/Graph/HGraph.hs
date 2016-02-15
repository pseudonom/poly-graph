{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Graph.HGraph
  ( module Data.Graph.HGraph
  , X.HGraph(Nil)
  ) where

import Data.Tagged
import GHC.TypeLits

import Data.Graph.HGraph.Internal as X

infixr 5 `Link`
class a `Link` b where
  infixr 5 `link`
  link :: a -> b -> a

infixr 5 :<:
pattern a :<: b <- Tagged a `Cons` b

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

data a :<: b
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
