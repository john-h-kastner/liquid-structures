module Heap.LeftistHeap where

--import Heap.Heap

{- TODO: ensure r is rank of heap. 
 - Other properties that might be checked:
 -}
{-@ data LeftistHeap a =
      E |
      T
        (r     :: {v:Nat | v > 0})
        (left  :: LH a)
        (right :: {v:LH a | (rank v == r - 1) &&
                            (rank left >= rank v)})
        (val   :: {v:a | IsMin v left && IsMin v right} )
  @-}

type LH a = LeftistHeap a
data LeftistHeap a = E | T Int (LH a) (LH a) a

{-@ predicate IsEmptyLH H = hsize H == 0 @-}
{-@ predicate IsMin N H = IsEmptyLH H || N <= (hmin H) @-}
 
{- I'm not sure that writing partial measures works well. If things start to
 - break, look here first. -}
{-@ measure hmin @-}
{-@ hmin :: forall a. {v:LH a | hsize v /= 0} -> a @-}
hmin (T _ _ _  v) = v

{-@ measure rank @-}
{-@ rank :: LH _ -> Nat @-}
rank :: LH a -> Int
rank E           = 0
rank (T r _ _ _) = r

{-@ makeT :: forall a.
      l:LH a                         ->
      r:LH a                         ->
      v:{a | IsMin v l && IsMin v r} ->
      {h:LH a | IsMin v h && (hsize h) == 1 + (hsize l) + (hsize r)}
  @-}
makeT :: LH a -> LH a -> a -> LH a
makeT l r v
  | rank l >= rank r = T (1 + rank r) l r v
  | otherwise        = T (1 + rank l) r l v

{-@ measure hsize @-}
{-@ hsize :: forall a.
      LH a ->
      Nat
  @-}
hsize :: LH a -> Int
hsize E           = 0
hsize (T _ l r _) = 1 + (hsize l) + (hsize r)

{-@ empty :: forall a. Ord a =>
      {h:LH a | 0 == hsize h}
  @-}
empty = E

{-@ isEmpty :: forall a. Ord a =>
      h:LH a ->
      {v:Bool | v <=> (0 == hsize h)} @-}
isEmpty E = True
isEmpty _ = False

{-@ findMin :: forall a. Ord a => 
      {h:LH a | hsize h /= 0} ->
      a
  @-}
findMin (T _ _ _ v) = v

{- I need this property to hold for my merge function. I don't actualy use
 - this directly but, having this property checked helped debug merge and it
 - might be usefull if things break in the future -}
{-@ lemma_LeMin :: forall a. Ord a => x : a -> y : a -> h : LH a ->
      {b:Bool | x <= y} ->
      {b:Bool | IsMin y h} ->
      {b:Bool | IsMin x h}
  @-}
lemma_LeMin :: Ord a => a -> a -> LH a -> Bool -> Bool -> Bool
lemma_LeMin _ _ _ _ _ = True

{- What I want this refinement type to say is "if some arbitrary element is
 - at least as small as then minimum of the input heaps, then it will be at
 - least as small as the minimum of the output heap."
 -
 - With the way I've written it at the moment, I need to introduce this
 - 'arbitrary element' as an extra argument. I would like to instead encode it
 - as a universal quantifier inside the refinement type for the output heap.
 -
 - Possible equivalent formulation: The minimum of the output heap is equal to
 - the minimum of one of the input heaps.
 -}
{-@ merge :: forall a. Ord a =>
      e:a ->
      h0:LH a ->
      h1:LH a ->
      {h2:LH a | (hsize h2 == hsize h0 + hsize h1) &&
                 (IsMin e h0 ==> IsMin e h1 ==> IsMin e h2)}
  @-}
merge :: Ord a => a -> LH a -> LH a -> LH a
merge _ h E = h
merge _ E h = h
merge e
      h1@(T _ a1 b1 x)
      h2@(T _ a2 b2 y)
      | x <= y    = makeT a1 (merge x b1 h2) x
      | otherwise = makeT a2 (merge y h1 b2) y

{-@ insert :: forall a. Ord a =>
      a ->
      h0:LH a ->
      {h1:LH a | hsize h1 == hsize h0 + 1}
  @-}
insert v h = merge v (T 1 E E v) h

{-@ deleteMin :: forall a. Ord a =>
      {h0:LH a | hsize h0 /= 0} ->
      {h1:LH a | hsize h1 == hsize h0 - 1}
  @-}
deleteMin (T _ r l v) = merge v r l
