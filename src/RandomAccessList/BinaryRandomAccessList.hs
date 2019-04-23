{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module RandomAccessList.BinaryRandomAccessList where

import Prelude hiding (head, tail, lookup)

import RandomAccessList.RandomAccessList

{-@ data Tree a =
      Leaf a |
      Node
        (left  :: Tree a)
        (right :: Tree a)
        (s     :: {v:Nat | v >= 2 && v == ((size left) + (size right))})
   @-}

data Tree a = Leaf a | Node (Tree a) (Tree a) Int deriving Eq
data Digit a = Zero | One (Tree a) deriving Eq
data BinaryList a = BL [Digit a] deriving Eq

{-@ measure size @-}
{-@ size :: forall a.
      Tree a -> 
      {n:Nat | n >= 1}
  @-}
size :: Tree a -> Int
size (Leaf _)     = 1
size (Node _ _ s) = s

{-@ link :: forall a.
      t0:Tree a ->
      t1:Tree a ->
      {t2:Tree a | (size t2) == (size t0) + (size t1)}
  @-}
link :: Tree a -> Tree a -> Tree a
link t0 t1 = Node t0 t1 (size t0 + size t1)

{-@ consTree :: forall a.
      t:Tree a     ->
      ds:[Digit a] ->
      {v:[Digit a] | len v == len ds || len v == 1 + len ds}
   @-}
consTree :: Tree a -> [Digit a] -> [Digit a]
consTree t []               = [One t]
consTree t (Zero : ts)      = (One t) : ts
consTree t0 ((One t1) : ts) = Zero : consTree (link t0 t1) ts

{- blLen and blSize are used to (hopefully) define the refinement type for
 - unconsTree. -}

{-@ measure blLen :: BinaryList a -> Nat
    blLen (BL l) = len l
  @-}

{- I feel like this should be able to work as a measure.
 - I tried a few different things but, all I got was incomprehensible
 - errors.-}

{-@ reflect blSize @-}
{-@ blSize :: bl:BinaryList a -> Nat / [blLen bl] @-}
blSize :: Eq a => BinaryList a -> Int
blSize (BL [])          = 0
blSize (BL ((One h):t)) = (size h) + (blSize (BL t))
blSize (BL (Zero:t))    = (blSize (BL t))

{- Making sure that the reflected blSize works how I think it should -}

{-@ test ::  {v:BinaryList Int | blSize v == 1} @-}
test :: BinaryList Int
test = BL [One (Leaf 1)]

{-@ test' ::  {v:BinaryList Int | blSize v == 0} @-}
test' :: BinaryList Int
test' = BL []

{-@ test'' ::  {v:BinaryList Int | blSize v == 0} @-}
test'' :: BinaryList Int
test'' = BL [Zero]

{-@ test''' ::  {v:BinaryList Int | blSize v == 3} @-}
test''' :: BinaryList Int
test''' = BL [Zero, One (Leaf 1), Zero, One (Node (Leaf 1) (Leaf 2) 2), Zero]

{-@ lemma_BLInject :: forall a.
      bl0 : BinaryList a ->
      l : {v:[Digit a] | (BL l) == bl0} ->
      {b:Bool | (BL l) == bl0}
  @-}
lemma_BLInject bl0 l = (BL l) == bl0

{-@ reflect cons_list @-}
cons_list x xs = x : xs

{- ':' is being interpreted as 'has type' instead of 'cons' -}
{-@ lemma_RemoveZero :: forall a.
    bl0 : {v:BinaryList a | blSize v > 0} ->
    l0 : {v:[Digit a] | (BL l0) == bl0} ->
    bl1 : BinaryList a ->
    l1 : {v:[Digit a] | (BL l1) == bl1 && (cons_list Zero l1) == l0} ->
    {b:Bool | (blSize l1) > 0} @-}
lemma_RemoveZero :: BinaryList a -> [Digit a] -> BinaryList a -> [Digit a] -> Bool
lemma_RemoveZero bl0 l0 bl1 l1 = True

--{-@ unconsTree :: forall a.
--      ds:{v:BinaryList a | blSize v > 0} ->
--      (Tree a, {v:BinaryList a | blSize v < blSize ds})
--      / [blLen ds]
--  @-}

--{-@ unconsTree :: forall a.
--      ds:{v:BinaryList a | blSize v > 0} ->
--      (Tree a, BinaryList a)
--      / [blLen ds]
--  @-}
--unconsTree :: BinaryList a -> (Tree a, BinaryList a)
--unconsTree (BL [One t])        = (t,BL [])
--unconsTree (BL ((One t) : ts)) = (t, BL (Zero : ts))
--unconsTree (BL (Zero : ts)) =
--  let ((Node t1 t2 _), (BL ts')) = unconsTree (BL ts) in 
--    (t1, BL ((One t2) : ts'))
--
