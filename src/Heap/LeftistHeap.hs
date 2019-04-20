module Heap.LeftistHeap where

--import Heap.Heap

{- TODO: ensure r is rank of heap. 
 - Other properties that might be checked:
 -   r > rank left && r > rank right 
 -   r == 1 + rank right
 -}
{-@ data LeftistHeap a =
      E |
      T
        (r     :: Nat)
        (left  :: LH a)
        (right :: {v:LH a | rank left >= rank v})
        (val   :: {v:a | IsMin v left && IsMin v right} )
  @-}

type LH a = LeftistHeap a
data LeftistHeap a = E | T Int (LH a) (LH a) a

{-@ predicate IsEmptyLH H = hsize H == 0 @-}
{-@ predicate IsMin N H = IsEmptyLH H || N <= (hmin H) @-}
{-@ predicate MinSmaller H0 H1 = IsMin (hmin H0) H1 @-}
 
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


{-@ merge :: forall a. Ord a =>
      h0:LH a ->
      h1:LH a ->
      {h2:LH a | IsEmptyLH h2 || (IsMin (hmin h2) h0 && IsMin (hmin h2) h1)}
  @-}
      --{h2:LH a | (hsize h2) == (hsize h0) + (hsize h1)}
merge :: Ord a => LH a -> LH a -> LH a
merge h E = h
merge E h = h
merge h1@(T _ a1 b1 x)
      h2@(T _ a2 b2 y) 
      | x <= y    = makeT a1 (merge b1 h2) x
      | otherwise = makeT a2 (merge h1 b2) y


      {- need: IsMin x (merge b1 h2) -}

      {- IsMin x h_a && IsMin x h_b ==> IsMin x (merge h_a h_b) -}

--insert v h = merge (T 1 E E v) h
--
--{-@ deleteMin :: forall a. Ord a =>
--      {h0:h a | hsize h0 /= 0} ->
--      {h1: h a | (hsize h1) == (hsize h0) - 1}
--  @-}
--deleteMin (T _ r l _) = merge r l



