module RandomAccessList.RandomAccessList where

import Prelude hiding (head, tail, lookup)

{-@ class measure rlen :: forall a. a -> {v:Int | v >= 0} @-}
{-@ class RandomAccessList r where
      empty   :: forall a.
        {r:(r a) | 0 == rlen r}
      isEmpty :: forall a.
        r:(r a) -> {v:Bool | v <=> (0 == rlen r)}

      cons    :: forall a.
        a -> r0:r a -> {r1:r a | (rlen r1) == (rlen r0) + 1}
      head    :: forall a.
        {r:r a | rlen r /= 0} -> a
      tail    :: forall a.
        {r0:r a | rlen r0 /= 0} -> {r1:r a | (rlen r1) == (rlen r0) - 1}

      lookup :: forall a.
        r:r a -> {i:Nat | i < rlen r} -> a
      update :: forall a.
        r0:r a -> {i:Nat | i < rlen r0} -> a -> {r1:r a | (rlen r1) == (rlen r1)}
  @-}

class RandomAccessList r where
  empty   :: r a
  isEmpty :: r a -> Bool

  cons    :: a -> r a -> r a
  head    :: r a -> a
  tail    :: r a -> r a

  lookup  :: r a -> Int -> a
  update  :: r a -> Int -> a -> r a
