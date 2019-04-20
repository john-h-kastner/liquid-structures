module Heap.Heap where

{-@ class measure hsize :: forall a. a -> Int @-}

{-@ class Heap h where
      empty     :: forall a. Ord a =>
        {h:h a | 0 == hsize h}
      isEmpty   :: forall a. Ord a =>
        h:h a -> {v:Bool | v <=> (0 == hsize h)}

      insert    :: forall a. Ord a =>
        a -> h0:h a -> {h1:h a | (hsize h1) == (hsize h0) + 1}
      merge     :: forall a. Ord a =>
        h0:h a -> h1:h a -> {h2:h a | (hsize h2) == (hsize h0) + (hsize h1)}

      findMin   :: forall a. Ord a =>
        {h:h a | hsize h /= 0} -> a
      deleteMin :: forall a. Ord a =>
        {h0:h a | hsize h0 /= 0} -> {h1: h a | (hsize h1) == (hsize h0) - 1}
  @-}

class Heap h where
  empty     :: Ord a => h a
  isEmpty   :: Ord a => h a -> Bool

  insert    :: Ord a => a -> h a -> h a
  merge     :: Ord a => h a -> h a -> h a

  findMin   :: Ord a => h a -> a
  deleteMin :: Ord a => h a -> h a
