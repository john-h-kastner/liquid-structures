{-@ LIQUID "--ple" @-}

module RandomAccessList.BinaryRandomAccessList where

import Prelude hiding (head, tail, lookup)

{- Defines the type for *complete* *binary* *leaf* trees -}
{-@ data Tree a =
        Leaf { val :: a }
      | Node {
          left  :: Tree a,
          right :: {v:Tree a | treeSize v == treeSize left},
          s     :: {v:Nat | v == (treeSize right) + (treeSize left)}
        }
  @-}
data Tree a =
    Leaf { val :: a }
  | Node {
      left  :: Tree a,
      right :: Tree a,
      s     :: Int
    } deriving Show

{-@ data Digit a =
        Zero
      | One {
          tree :: Tree a
        }
  @-}
data Digit a =
    Zero
  | One {
      tree :: Tree a
    } deriving Show

{- I think that defining a custom list data type will be easier than using a
 - wrapper around the builtin type -}
{-@ data BinaryList a =
      Nil {
        nil_idx :: Nat
      }
    | Cons {
       idx :: Nat,
       hd  :: {v:Digit a | (isOne v) ==> (treeSize (tree v) == pow2 idx)},
       tl  :: {v:BinaryList a | (getIndex v) == idx + 1}
      }
  @-}
data BinaryList a =
    Nil {
      nil_idx :: Int
    }
  | Cons {
      idx :: Int,
      hd  :: Digit a,
      tl  :: BinaryList a
    } deriving Show

{- A complete list as a result of a cons, tail or similar operation should
 - start at index 0. This constraint is omitted from the main data type since
 - partial lists are required for the recursive data definition and recursive
 - functions -}
{-@ type CompleteBinaryList a = {v:BinaryList a | getIndex v == 0} @-}

{-@ reflect pow2 @-}
{-@ pow2 :: Nat -> Nat @-}
pow2 :: Int -> Int
pow2 0 = 1
pow2 n = 2 * (pow2 (n - 1))

{-@ measure getIndex @-}
{-@ getIndex ::
      bl:BinaryList a ->
      {v:Nat |
        if (listLen bl) == 0 then
          v == (nil_idx bl)
        else
          v == (idx bl)}
  @-}
getIndex :: BinaryList a -> Int
getIndex (Nil idx)      = idx
getIndex (Cons idx _ _) = idx

{- Calculate the number of elements in a tree. Since these are leaf trees, the
 - number of elements is equal to the number of leaves in the tree. This should
 - only be used as a measure. For getting the size of a tree at run time, use
 - cachedTreeSize -}
{-@ measure treeSize @-}
{-@ treeSize :: Tree a -> Nat @-}
treeSize :: Tree a -> Int
treeSize (Leaf _)     = 1
treeSize (Node l r _) = (treeSize l) + (treeSize r)

{- The tree type stores the size of the tree. Rather than computing it, we can
 - just return this stored value. -}
{-@ cachedTreeSize :: t:Tree a -> {v:Nat | v == treeSize t} @-}
cachedTreeSize :: Tree a -> Int
cachedTreeSize (Leaf _)     = 1
cachedTreeSize (Node _ _ s) = s

{- Calculate the raw lenght of a Binarylist. In this calculation, each tree
 - counts once. See list_size for counting total elements across all trees.-}
{-@ measure listLen @-}
{-@ listLen :: BinaryList a -> Nat @-}
listLen :: BinaryList a -> Int
listLen (Nil _)      = 0
listLen (Cons _ _ t) = 1 + listLen t

{-@ measure binListLen @-}
{-@ binListLen :: BinaryList a -> Nat @-}
binListLen :: BinaryList a -> Int
binListLen (Nil _)      = 0
binListLen (Cons _ h t) =
  (if isOne h then treeSize (getOne h) else 0) + (binListLen t)

{-@ measure isOne @-}
{-@ isOne :: Digit a -> Bool @-}
isOne :: Digit a -> Bool
isOne Zero    = False
isOne (One _) = True

{-@ measure getOne @-}
{-@ getOne :: {v:Digit a | isOne v} -> Tree a @-}
getOne :: Digit a -> Tree a
getOne (One t) = t

{-@ link ::
       t0:Tree a ->
       t1:{v:Tree a | treeSize t0 == treeSize v} ->
       {v:Tree a | treeSize v == (treeSize t0 + treeSize t1)}
  @-}
link :: Tree a -> Tree a -> Tree a
link t0 t1 = Node t0 t1 (treeSize t0 + treeSize t1)

{-@ consTree ::
      t:Tree a ->
      b:{v:BinaryList a | pow2 (getIndex v) == treeSize t} ->
      {v:BinaryList a | getIndex v == getIndex b &&
                        binListLen v = (treeSize t) + (binListLen b)}
  @-}
consTree :: Tree a -> BinaryList a -> BinaryList a
consTree t (Nil s)               = Cons s (One t) (Nil (s + 1))
consTree t (Cons s Zero ts)      = Cons s (One t) ts
consTree t0 (Cons s (One t1) ts) = Cons s Zero (consTree (link t0 t1) ts)

{-@ unconsTree ::
      b:{v:BinaryList a | binListLen v /= 0} ->
      ({v:Tree a | pow2 (getIndex b) == treeSize v}, 
       {v:BinaryList a | getIndex v == getIndex b &&
                         binListLen v == binListLen b - pow2 (getIndex b)})
  @-}
unconsTree :: BinaryList a -> (Tree a, BinaryList a)
unconsTree (Cons s (One h) (Nil _)) = (h, Nil s)
unconsTree (Cons s (One h) t)       = (h, Cons s Zero t)
unconsTree (Cons s Zero t)          = 
  let (Node tl tr _, t') = unconsTree t in
  (tl, Cons s (One tr) t')

{-@ empty :: forall a. {r:CompleteBinaryList a | 0 == binListLen r} @-}
empty = Nil 0

{-@ isEmpty :: forall a. r:(CompleteBinaryList a) -> {v:Bool | v <=> (0 == binListLen r)} @-}
isEmpty bl = 0 == binListLen bl

{-@ cons :: forall a. a -> r0:CompleteBinaryList a -> {r1:CompleteBinaryList a | (binListLen r1) == (binListLen r0) + 1} @-}
cons e bl = consTree (Leaf e) bl

{-@ head :: forall a. {r:CompleteBinaryList a | binListLen r /= 0} -> a @-}
head bl = let (Leaf e, _) = unconsTree bl in e

{- I don't know why but, liquid won't do this substitutoin inline without
 - explicitly referencing the lemma -}
{-@ lemma_pow2_0 :: b:CompleteBinaryList a ->  {v:() | 1 == pow2 (getIndex b)} @-}
lemma_pow2_0 :: BinaryList a -> ()
lemma_pow2_0 _ = ()

{-@ tail ::
      r:{v:CompleteBinaryList a | binListLen v /= 0} ->
      {v:CompleteBinaryList a | (binListLen v) == (binListLen r) - 1}
  @-}
tail bl = let (_, t) = unconsTree bl in (flip const) (lemma_pow2_0 bl) $ t

--{-@ lookup  :: forall a. r:r a -> {i:Nat | i < rlen r} -> a @-}
--{-@ update  :: forall a. r0:r a -> {i:Nat | i < rlen r0} -> a -> {r1:r a | (rlen r1) == (rlen r1)} @-}
