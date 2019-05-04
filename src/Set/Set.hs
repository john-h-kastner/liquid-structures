{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Set.Set where

import qualified Data.Set as Set

{-@ class measure setElts :: forall s a. s a -> Set.Set a @-}

{-@ class Set s a where
      empty  :: {v:s a | Set_emp (setElts v)}
      insert :: e:a -> v:s a -> {vv: s a | (setElts vv) == Set_cup (Set_sng e) (setElts v)}
      member :: e:a -> v:s a -> Bool
  @-}

class Set s a where
  empty  :: s a
  insert :: a -> s a -> s a
  member :: a -> s a -> Bool

{------------------------------------------------------------------------------
 - BEGIN UnbalancedSet Implementation
 - I couldn't get this to work in a seperate file so, it's here for now.
 -----------------------------------------------------------------------------}

{-@ data UnbalancedSet a =
      E |
      T {
        val   :: a,
        left  :: UnbalancedSet {vv:a | vv < val},
        right :: UnbalancedSet {vv:a | vv > val}
      }
@-}

data UnbalancedSet a =
  E |
  T {
    val   :: a,
    left  :: UnbalancedSet a,
    right :: UnbalancedSet a
  }

{-@ instance measure setElts :: forall a. UnbalancedSet a -> Set.Set a
    setElts E         = (Set_empty 0)
    setElts (T v l r) = Set_cup (Set_sng v) (Set_cup (setElts l) (setElts r))
  @-}

{-@ insert_aux :: Ord a =>
      x:a ->
      v:UnbalancedSet a ->
      {vv: UnbalancedSet a |
         ((setElts vv) == Set_cup (Set_sng x) (setElts v))}
 @-}
insert_aux :: Ord a => a -> UnbalancedSet a -> UnbalancedSet a
insert_aux x E = T x E E
insert_aux x s@(T y l r)
  | x < y     = T y (insert_aux x l) r
  | x > y     = T y l (insert_aux x r)
  | otherwise = s

instance Ord a => Set UnbalancedSet a where
  empty = E

  insert x s = insert_aux x s

  member _ E = False
  member x (T y l r)
    | x < y     = member x l
    | x > y     = member x r
    | otherwise = True

{------------------------------------------------------------------------------
 - BEGIN Red-Black Implementation
 - Same story as above.
 -----------------------------------------------------------------------------}

data Color = Red | Black deriving Eq

{-@ data RedBlackSet a =
      Empty |
      Tree {
        color   :: Color,
        rbval   :: a,
        rbleft  :: { v:RedBlackSet {vv:a | vv < rbval} | RedInvariant color v},
        rbright :: { v:RedBlackSet {vv:a | vv > rbval} | RedInvariant color v &&
                                                         BlackInvariant v rbleft}
      }
   @-}

{-@ predicate RedInvariant C S     = (C == Red) ==> (getColor S /= Red) @-}
{-@ predicate BlackInvariant S0 S1 = (numBlack S0) == (numBlack S1) @-}

data RedBlackSet a =
  Empty |
  Tree {
    color   :: Color,
    rbval   :: a,
    rbleft  :: RedBlackSet a,
    rbright :: RedBlackSet a
  }

{- Assuming that the number of black nodes along are paths to a leaf node are
 - equal, return this value. This function actually counts the number of black
 - nodes when recursing leftwards down the tree but, red black tree must have
 - this value be the same for all paths to a leaf node -}
{-@ measure numBlack @-}
{-@ numBlack :: RedBlackSet a -> Nat @-}
numBlack :: RedBlackSet a -> Int
numBlack Empty          = 0
numBlack (Tree c _ l r) = (if c == Black then 1 else 0) + (numBlack l)

{- By definition, the empty nodes in a Red Black Tree are black. The color of
 - all other nodes is defined by the color field -}
{-@ measure getColor @-}
{-@ getColor :: RedBlackSet a -> Color @-}
getColor Empty          = Black
getColor (Tree c _ _ _) = c

{-@ instance measure setElts :: forall a. RedBlackSet a -> Set.Set a
    setElts Empty          = (Set_empty 0)
    setElts (Tree _ v l r) = Set_cup (Set_sng v) (Set_cup (setElts l) (setElts r))
  @-}

{- Sometimes, I need to represent a weaker variant of a RedBlackSet. This data
 - type checks most of the same invariants but, it does not require that the 
 - red invariant holds for the root of the tree. It does require that the black
 - invariant holds.
 -
 - It also a requires a weak version of the red invariant: At least one out of
 - the root node and its children must be black. This property was chosen
 - because it holds for trees before and after rebalancing during insertion. -}

{-@ data WeakRedInvariant a = WeakRedInvariant {
        weakColor :: Color,
        weakVal   :: a,
        weakLeft  :: RedBlackSet {vv:a | vv < weakVal},
        weakRight :: {v:RedBlackSet {vv:a | vv > weakVal} |
          (weakColor /= Red || 
          (getColor weakLeft) /= Red ||
          (getColor v) /= Red) &&
          (numBlack v) == (numBlack weakLeft)}
      }
  @-}

data WeakRedInvariant a = WeakRedInvariant {
  weakColor :: Color,
  weakVal   :: a,
  weakLeft  :: RedBlackSet a,
  weakRight :: RedBlackSet a
}

{- I want to be able to say that a WeakRedInvariant actualy has the original 
 - strong version of the invariant. -}
{-@ predicate HasStrongRedInvariant Nri = (weakColor Nri) == Red ==>
                                            (getColor (weakLeft Nri) /= Red &&
                                             getColor (weakRight Nri) /= Red)
  @-}

{-@ instance measure setElts :: forall a. WeakRedInvariant a -> Set.Set a
    setElts (WeakRedInvariant _ v l r) = Set_cup (Set_sng v) (Set_cup (setElts l) (setElts r))
  @-}

{-@ measure weakNumBlack @-}
{-@ weakNumBlack :: WeakRedInvariant a -> Nat @-}
weakNumBlack :: WeakRedInvariant a -> Int
weakNumBlack (WeakRedInvariant c _ l r) = (if c == Black then 1 else 0) + (numBlack l)

{- balanceLeft is called after the recursivly inserting an element into the left
 - subtree. The recursive insert might have left the tree in a state where the
 - red invariant no longer holds. This Fixes the invariant in the left subtree
 - and returns a new tree constructed using the element, right subtree and fixed
 - left subtree. This new tree might also fail to maintain the red invariant. but,
 - this will be fixed by later calls to balance or by insert after rb_insert_aux
 - completes. -}
{-@ balanceLeft :: forall a. Ord a =>
      c:Color ->
      t:a ->
      l:{v:WeakRedInvariant {vv:a | vv < t} | c == Red ==> HasStrongRedInvariant v} ->
      r:{v:RedBlackSet {vv:a | vv > t} | RedInvariant c v &&
                                         (numBlack v) == (weakNumBlack l)} ->
      {v:WeakRedInvariant a | (c /= Red ==> HasStrongRedInvariant v) &&
                              (weakNumBlack v) == ( if c == Black then 1 else 0) + weakNumBlack l &&
                              (setElts v) == (Set_cup (Set_sng t) (Set_cup (setElts l) (setElts r)))}
  @-}
balanceLeft :: Ord a => Color -> a -> WeakRedInvariant a -> RedBlackSet a -> WeakRedInvariant a
balanceLeft Black z (WeakRedInvariant Red y (Tree Red x a b) c) d =
  WeakRedInvariant Red y (Tree Black x a b) (Tree Black z c d)

balanceLeft Black z (WeakRedInvariant Red x a (Tree Red y b c)) d =
  WeakRedInvariant Red y (Tree Black x a b) (Tree Black z c d)

balanceLeft c x (WeakRedInvariant c' x' a' b' ) b =
  WeakRedInvariant c x (Tree c' x' a' b') b

{- balanceRight has the same logic as balanceLeft but, it is called after inserting
 - into the right subtree. -}
{-@ balanceRight :: forall a. Ord a =>
      c:Color ->
      t:a ->
      l:{v:RedBlackSet {vv:a | vv < t} | RedInvariant c v} ->

      r:{v:WeakRedInvariant {vv:a | vv > t} | (c == Red ==> HasStrongRedInvariant v) &&
                                              (weakNumBlack v) == (numBlack l)} ->

      {v:WeakRedInvariant a | (c /= Red ==> HasStrongRedInvariant v) &&
                              (weakNumBlack v) == (if c == Black then 1 else 0) + numBlack l &&
                              (setElts v) == (Set_cup (Set_sng t) (Set_cup (setElts l) (setElts r)))}
   @-}
balanceRight :: Ord a => Color -> a -> RedBlackSet a -> WeakRedInvariant a -> WeakRedInvariant a
balanceRight Black x a (WeakRedInvariant Red z (Tree Red y b c) d ) =
  WeakRedInvariant Red y (Tree Black x a b) (Tree Black z c d)

balanceRight Black x a (WeakRedInvariant Red y b (Tree Red z c d) ) =
  WeakRedInvariant Red y (Tree Black x a b) (Tree Black z c d)

balanceRight c x a (WeakRedInvariant c' x' a' b' ) =
  WeakRedInvariant c x a (Tree c' x' a' b')

{- This is where recursive insertion happens. No special refinements are placed
 - on the inputs to this function, but the return type is interesting. The return
 - value is not always a complete red back tree. It only has the full red invariant
 - if the original color of the tree was black (I'm not sure I fully understand
 - why this is the case). The other refinements on the return value check that
 - the black node property has not changed during insertion and that the expected
 - change has occurred in the set of elements. The first is required when constructing
 - a new tree from the old subtree and a new subtree where an element has been inserted.
 - The second is used to ensure this data structure behaves like a set. -}
{-@ rb_insert_aux :: forall a. Ord a =>
      x:a ->
      s:RedBlackSet a ->
      {v:WeakRedInvariant a | ((getColor s) /= Red ==> HasStrongRedInvariant v) &&
                              (weakNumBlack v) == (numBlack s) &&
                              (setElts v) == (Set_cup (Set_sng x) (setElts s))}
  @-}
rb_insert_aux :: Ord a => a -> RedBlackSet a -> WeakRedInvariant a
rb_insert_aux x Empty = WeakRedInvariant Red x Empty Empty
rb_insert_aux x (Tree c y a b)
  | x < y     = balanceLeft c y (rb_insert_aux x a) b
  | x > y     = balanceRight c y a (rb_insert_aux x b)
  | otherwise = (WeakRedInvariant c y a b)

instance Ord a => Set RedBlackSet a where
  empty = Empty

  {- The result of rb_insert_aux might not have the red invaraint. This is easy
   - to fix by forceing the root node to be black -}
  insert x s = forceRedInvarient (rb_insert_aux x s)
    where forceRedInvarient (WeakRedInvariant _ e a b) = Tree Black e a b

  member _ Empty = False
  member e (Tree _ x l r)
    | e < x     = member e l
    | e > x     = member e r
    | otherwise = True
