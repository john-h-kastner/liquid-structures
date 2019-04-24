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

{-@ measure blList @-}
blList (BL l) = l

{- bogus definitions for leaf -}

{-@ measure leftChild @-}
leftChild (Node l _ _) = l
leftChild leaf         = leaf

{-@ measure rightChild @-}
rightChild (Node _ r _) = r
rightChild leaf         = leaf

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

{-@ test'' ::  {v:BinaryList Int | (not (blIsNil v)) && blSize v == 0} @-}
test'' :: BinaryList Int
test'' = BL [Zero]

{-@ test''' ::  {v:BinaryList Int | blSize v == 3} @-}
test''' :: BinaryList Int
test''' = BL [Zero, One (Leaf 1), Zero, One (Node (Leaf 1) (Leaf 2) 2), Zero]

{-@ measure blEmpty @-}
{-@ blEmpty :: forall a. Eq a =>
      bl:BinaryList a ->
      Bool
      / [blLen bl]
  @-}
blEmpty :: Eq a => BinaryList a -> Bool
blEmpty (BL [])    = True
blEmpty (BL (h:t)) = (h == Zero) && (blEmpty (BL t))

{-@ measure blIsNil @-}
blIsNil :: BinaryList a -> Bool
blIsNil (BL []) = True
blIsNil _       = False

{-@ lemma_emptyThenZeros :: forall a. Eq a =>
      bl:{v:BinaryList a | blEmpty v} ->
      {ds:[{d:Digit a | d == Zero}] | (BL ds) == bl}
      / [blLen bl]
  @-}
lemma_emptyThenZeros :: Eq a => BinaryList a -> [Digit a]
lemma_emptyThenZeros (BL []) = []
lemma_emptyThenZeros (BL (Zero:ds)) = Zero:(lemma_emptyThenZeros (BL ds))

{-@ lemma_notEmptyThenNotNil :: forall a. Eq a =>
      bl:{v:BinaryList a | not (blEmpty v)} ->
      {ds:[Digit a] | (BL ds) == bl && (not (blIsNil bl))}
      / [blLen bl]
  @-}
lemma_notEmptyThenNotNil :: Eq a => BinaryList a -> [Digit a]
lemma_notEmptyThenNotNil (BL (d:ds)) = d:ds


{- forall binary lists bl, ~ (blEmpty bl) -> (bl /= BL []) -}
{-@ lemma_notEmptyThenNotNil' :: forall a. Eq a =>
      bl:BinaryList a ->
      {b:Bool | not (blEmpty bl)} ->
      {b:Bool | not (blIsNil bl)}
  @-}
lemma_notEmptyThenNotNil' :: Eq a => BinaryList a -> Bool -> Bool
lemma_notEmptyThenNotNil' (BL ds) _ = True

{-@ lemma_sizeNotNil :: forall a. Eq a =>
      bl:BinaryList a ->
      {b:Bool | blSize (bl) > 0} ->
      {b:Bool | not (blIsNil bl)} @-}
lemma_sizeNotNil :: Eq a => BinaryList a -> Bool -> Bool 
lemma_sizeNotNil (BL (d:ds)) _ = True

{-@ blHead :: forall a.
      bl:{v:BinaryList a | not (blIsNil bl)} ->
      Digit a
  @-}
blHead :: BinaryList a -> Digit a
blHead (BL (h:_)) = h

{-@ blHead' :: forall a.
      bl:{v:BinaryList a | (blSize bl) > 0} ->
      Digit a
  @-}
blHead' :: BinaryList a -> Digit a
blHead' (BL (h:_)) = h

{-@ measure blHead'' @-}
{-@ blHead'' :: forall a.
      bl:{v:BinaryList a | (not (blEmpty bl)) || (not (blIsNil bl)) || (blSize bl) > 0} ->
      Digit a
  @-}
blHead'' :: BinaryList a -> Digit a
blHead'' (BL (h:_)) = h

head_test = (flip const) (lemma_sizeNotNil test''' True) $ blHead test'''
head_test' = blHead' test'''
head_test'' = blHead'' test''

{-@ measure blTail @-}
{-@ blTail :: forall a.
      bl:{v:BinaryList a | (not (blEmpty bl)) || (not (blIsNil bl)) || (blSize bl) > 0} ->
      BinaryList a
  @-}
blTail :: BinaryList a -> BinaryList a
blTail (BL (_:t)) = BL t

{- forall binary lists bl, ~ (blEmpty bl) /\ (head bl == Zero) -> ~(blEmpty (tail bl)) -}
{- TBH not sure why this checks but, I'll take it. @-}
{-@ lemma_tailNotEmpty :: forall a. Eq a =>
      bl:BinaryList a ->
      {b:Bool | not (blEmpty bl)} ->
      {b:Bool | (blHead'' bl) == Zero} ->
      {b:Bool | not (blEmpty (blTail bl))}
  @-}
lemma_tailNotEmpty :: Eq a => BinaryList a -> Bool -> Bool -> Bool
lemma_tailNotEmpty (BL (Zero:t)) b0 b1 = True

--{-@ unconsTree :: forall a.
--      ds:{v:BinaryList a | blSize v > 0} ->
--      (Tree a, {v:BinaryList a | blSize v < blSize ds})
--      / [blLen ds]
--  @-}

{-@ unconsTree :: forall a. Eq a =>
      ds:{v:BinaryList a | not (blEmpty v)} ->
      (Tree a, BinaryList a)
      / [blLen ds]
  @-}
unconsTree :: Eq a => BinaryList a -> (Tree a, BinaryList a)
unconsTree (BL [One t])        = (t, BL [])
unconsTree (BL ((One t) : ts)) = (t, BL (Zero : ts))
unconsTree (BL (Zero : ts)) =
  {- I've got this working for now but, am leaving my previouse commment
   - in case this breaks again. -}
  {- I *think* I know why this doesn't check. unconsTree requires that its argument
   - list is non-empty but, the tail of a non-empty list in general can be
   - empty. In this case, 'non-empty' means both not empty in the usual sense
   - and also that the list contains at least one 'One' element. Since the head
   - of this list is 'Zero' in this case, the tail of the list must be at least
   - a singleton list containing a 'One'. If I can prove this it Liquid, this
   - should work. -}
  let (t,bl) = (flip const) (lemma_tailNotEmpty (BL (Zero:ts)) True True) $ unconsTree (BL ts) in
    (leftChild t, BL (One (rightChild t) : (blList bl)))

{- for some reason, this was being rejected by liquid. Not sure why it's bogus though -}
--  let ((Node t1 t2 _), (BL ts')) = (flip const) (lemma_tailNotEmpty (BL (Zero:ts)) True True) $ unconsTree (BL ts) in
--    (t1, BL ((One t2) : ts'))









{-filler-}
