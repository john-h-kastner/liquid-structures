module RandomAccessList.BinaryRandomAccessList where

import RandomAccessList.RandomAccessList

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
        nil_size :: {v:Nat | v > 0}
      }
    | Cons {
       size :: {v:Nat | v > 0},
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
{-@ data CompleteBinaryList a =
      CBL {
        bl :: {v:BinaryList a | getSize v == 1}
      }
  @-}
data CompleteBinaryList a =
  CBL {
    bl :: (BinaryList a)
  }

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
{-@ treeSize :: Tree a -> {v:Nat | v > 0} @-}
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

{-@ lookupBL ::
      b:BinaryList a ->
      {i:Nat | i < binListLen b} ->
      a
  @-}
lookupBL :: BinaryList a -> Int -> a
lookupBL (Cons size Zero ts) i  = lookupBL ts i
lookupBL (Cons size (One t) ts) i
  | i < size   = lookupTree t i
  | otherwise  = lookupBL ts (i - size)

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

{-@ updateBL ::
      b:BinaryList a ->
      {i : Nat  | i < binListLen b} ->
      a ->
      {b':BinaryList a | (getSize b') == (getSize b) &&
                         (binListLen b') == (binListLen b)}
  @-}
updateBL :: BinaryList a -> Int -> a -> BinaryList a
updateBL (Cons size Zero ts) i e = Cons size Zero (updateBL ts i e)
updateBL (Cons size (One t) ts) i e
   | i < size  = Cons size (One $ updateTree t i e) ts
   | otherwise = Cons size (One t) $ updateBL ts (i - size) e

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

instance RandomAccessList CompleteBinaryList where
  {-@ instance measure rlen :: CompleteBinaryList a -> {v:Int | v >= 0}
      rlen (CBL bl) = binListLen bl
    @-}

  empty = CBL $ Nil 1
  isEmpty (CBL bl) = 0 == binListLen bl

  cons e (CBL bl) = CBL $ consTree (Leaf e) bl
  head (CBL bl) = let (Leaf e, _) = unconsTree bl in e
  tail (CBL bl) = let (_, t) = unconsTree bl in CBL t

  lookup (CBL bl) e =  lookupBL bl e
  update (CBL bl) i e = CBL $ updateBL bl i e
