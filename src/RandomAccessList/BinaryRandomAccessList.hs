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
        nil_size :: Nat
      }
    | Cons {
       size :: Nat,
       hd   :: {v:Digit a | (isOne v) ==> (treeSize (tree v) == size)},
       tl   :: {v:BinaryList a | (getSize v) == size * 2}
      }
  @-}
data BinaryList a =
    Nil {
      nil_size :: Int
    }
  | Cons {
      size :: Int,
      hd   :: Digit a,
      tl   :: BinaryList a
    } deriving Show

{- A complete list as a result of a cons, tail or similar operation should
 - start at index 0. This constraint is omitted from the main data type since
 - partial lists are required for the recursive data definition and recursive
 - functions -}
{-@ type CompleteBinaryList a = {v:BinaryList a | getSize v == 1} @-}

{-@ measure getSize @-}
{-@ getSize ::
      bl:BinaryList a ->
      {v:Nat |
        if (listLen bl) == 0 then
          v == (nil_size bl)
        else
          v == (size bl)}
  @-}
getSize :: BinaryList a -> Int
getSize (Nil size)      = size
getSize (Cons size _ _) = size

{- Calculate the number of elements in a tree. Since these are leaf trees, the
 - number of elements is equal to the number of leaves in the tree. This should
 - only be used as a measure. For getting the size of a tree at run time, use
 - cachedTreeSize -}
{-@ measure treeSize @-}
{-@ treeSize :: Tree a -> Nat @-}
treeSize :: Tree a -> Int
treeSize (Leaf _)     = 1
treeSize (Node l r _) = (treeSize l) + (treeSize r)

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
      b:{v:BinaryList a | getSize v == treeSize t} ->
      {v:BinaryList a | getSize v == getSize b &&
                        binListLen v = (treeSize t) + (binListLen b)}
  @-}
consTree :: Tree a -> BinaryList a -> BinaryList a
consTree t (Nil s)               = Cons s (One t) (Nil (s * 2))
consTree t (Cons s Zero ts)      = Cons s (One t) ts
consTree t0 (Cons s (One t1) ts) = Cons s Zero (consTree (link t0 t1) ts)

{-@ unconsTree ::
      b:{v:BinaryList a | binListLen v /= 0} ->
      ({v:Tree a | getSize b == treeSize v}, 
       {v:BinaryList a | getSize v == getSize b &&
                         binListLen v == binListLen b - getSize b})
  @-}
unconsTree :: BinaryList a -> (Tree a, BinaryList a)
unconsTree (Cons s (One h) (Nil _)) = (h, Nil s)
unconsTree (Cons s (One h) t)       = (h, Cons s Zero t)
unconsTree (Cons s Zero t)          = 
  let (Node tl tr _, t') = unconsTree t in
  (tl, Cons s (One tr) t')

{-@ empty :: {r:CompleteBinaryList a | 0 == binListLen r} @-}
empty = Nil 1

{-@ isEmpty ::
      r:(CompleteBinaryList a) ->
      {v:Bool | v <=> (0 == binListLen r)}
  @-}
isEmpty bl = 0 == binListLen bl

{-@ cons ::
      a ->
      r0:CompleteBinaryList a ->
      {r1:CompleteBinaryList a | (binListLen r1) == (binListLen r0) + 1}
  @-}
cons e bl = consTree (Leaf e) bl

{-@ head ::
      {r:CompleteBinaryList a | binListLen r /= 0} ->
      a
  @-}
head bl = let (Leaf e, _) = unconsTree bl in e

{-@ tail ::
      r:{v:CompleteBinaryList a | binListLen v /= 0} ->
      {v:CompleteBinaryList a | (binListLen v) == (binListLen r) - 1}
  @-}
tail bl = let (_, t) = unconsTree bl in t

{-@ lookup ::
      b:BinaryList a ->
      {i:Nat | i < binListLen b} ->
      a
  @-}
lookup :: BinaryList a -> Int -> a
lookup (Cons size Zero ts) i  = lookup ts i
lookup (Cons size (One t) ts) i
  | i < size   = lookupTree t i
  | otherwise  = lookup ts (i - size)

{-@ lookupTree ::
      t:Tree a ->
      {i:Nat | i < treeSize t} ->
      a
  @-}
lookupTree :: Tree a -> Int -> a
lookupTree (Leaf x) 0 = x
lookupTree (Node tl tr w) i
  | i < (w `div` 2) = lookupTree tl i
  | otherwise       = lookupTree tr (i - w `div` 2)

{-@ update ::
      b:BinaryList a ->
      {i : Nat  | i < binListLen b} ->
      a ->
      {b':BinaryList a | (getSize b') == (getSize b) &&
                         (binListLen b') == (binListLen b)}
  @-}
update :: BinaryList a -> Int -> a -> BinaryList a
update (Cons size Zero ts) i e = Cons size Zero (update ts i e)
update (Cons size (One t) ts) i e
   | i < size  = Cons size (One $ updateTree t i e) ts
   | otherwise = Cons size (One t) $ update ts (i - size) e

{-@ updateTree ::
      t:Tree a ->
      {i:Nat | i < treeSize t} ->
      a ->
      {t':Tree a | (treeSize t') == (treeSize t)}
  @-}
updateTree :: Tree a -> Int -> a -> Tree a
updateTree (Leaf _) 0 e  = (Leaf e)
updateTree (Node tl tr w) i e
  | i < w `div` 2 = Node (updateTree tl i e) tr w
  | otherwise     = Node tl (updateTree tr (i - w `div` 2) e) w
