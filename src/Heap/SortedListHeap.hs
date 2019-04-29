module Heap.SortedListHeap where

{-@ data SortedListHeap a =
      Nil |
      Cons {
        t :: SLH a,
        h :: {v:a | IsMin v t}
      }
  @-}

type SLH a = SortedListHeap a
data SortedListHeap a =
  Nil |
  Cons {
    t :: SLH a,
    h :: a
  }

{-@ predicate IsEmptyLH H = hsize H == 0 @-}
{-@ predicate IsMin N H = IsEmptyLH H || N <= (hmin H) @-}

{-@ measure hmin @-}
{-@ hmin :: forall a. {v:SLH a | hsize v /= 0} -> a @-}
hmin (Cons _ v) = v

{-@ measure hsize @-}
{-@ hsize :: SLH a -> Nat @-}
hsize :: SLH a -> Int
hsize Nil        = 0
hsize (Cons t _) = 1 + (hsize t) 

{-@ empty :: forall a. Ord a =>
      {h:SLH a | 0 == hsize h}
  @-}
empty = Nil

{-@ isEmpty :: forall a. Ord a =>
      h:SLH a ->
      {v:Bool | v <=> (0 == hsize h)} @-}
isEmpty Nil        = True
isEmpty (Cons _ _) = False

{-@ insert :: forall a. Ord a =>
      a ->
      h0:SLH a ->
      {h1:SLH a | (hsize h1) == (hsize h0) + 1}
  @-}
insert e l = merge (Cons Nil e) l

{-@ merge_aux :: forall a. Ord a =>
      e:a ->
      h0:SLH a ->
      h1:SLH a ->
      {h2:SLH a | (hsize h2) == (hsize h0) + (hsize h1) &&
                  (IsMin e h0 ==> IsMin e h1 ==> IsMin e h2)}
  @-}
merge_aux :: Ord a => a -> SLH a -> SLH a -> SLH a
merge_aux _ Nil h1 = h1
merge_aux _ h0 Nil = h0
merge_aux _ h0@(Cons t0 v0)
        h1@(Cons t1 v1)
  | v0 < v1   = Cons (merge_aux v0 t0 h1) v0
  | otherwise = Cons (merge_aux v1 h0 t1) v1

{-@ merge :: forall a. Ord a =>
      h0:SLH a ->
      h1:SLH a ->
      {h2:SLH a | (hsize h2 == hsize h0 + hsize h1)}
  @-}
merge Nil Nil = Nil
merge h0@(Cons _ x) h1 = merge_aux x h0 h1
merge h0 h1@(Cons _ y) = merge_aux y h0 h1

{-@ findMin :: forall a. Ord a =>
      {h:SLH a | hsize h /= 0} ->
      a
  @-}
findMin (Cons _ v) = v

{-@ deleteMin :: forall a. Ord a =>
      {h0:SLH a | hsize h0 /= 0} ->
      {h1: SLH a | (hsize h1) == (hsize h0) - 1}
  @-}
deleteMin (Cons t _) = t
