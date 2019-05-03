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
        left  :: {v : UnbalancedSet a | IsGT val v},
        right :: {v : UnbalancedSet a | IsLT val v}
      }
@-}

data UnbalancedSet a =
  E |
  T {
    val   :: a,
    left  :: UnbalancedSet a,
    right :: UnbalancedSet a
  }

{-@ predicate IsGT N S = isEmpty S || N > (usTop S) @-}
{-@ predicate IsLT N S = isEmpty S || N < (usTop S) @-}

{-@ measure usTop @-}
{-@ usTop :: forall a. {v:UnbalancedSet a | not (isEmpty v)} -> a @-}
usTop :: UnbalancedSet a -> a
usTop (T v _ _) = v

{-@ measure isEmpty @-}
{-@ isEmpty :: v:UnbalancedSet a -> {b:Bool | b <=> Set_emp (setElts  v)} @-}
isEmpty E = True
isEmpty _ = False

{-@ instance measure setElts :: forall a. UnbalancedSet a -> Set.Set a
    setElts E         = (Set_empty 0)
    setElts (T v l r) = Set_cup (Set_sng v) (Set_cup (setElts l) (setElts r))
  @-}

{-@ insert_aux :: Ord a =>
      y:a ->
      x:a ->
      v:UnbalancedSet a ->
      {vv: UnbalancedSet a |
         (x < y ==> IsGT y v ==> IsGT y vv) &&
         (x > y ==> IsLT y v ==> IsLT y vv) &&
         ((setElts vv) == Set_cup (Set_sng x) (setElts v))}
 @-}
insert_aux :: Ord a => a -> a -> UnbalancedSet a -> UnbalancedSet a
insert_aux _ x E    = T x E E
insert_aux _ x s@(T y l r)
  | x < y     = T y (insert_aux y x l) r
  | x > y     = T y l (insert_aux y x r)
  | otherwise = s

instance Ord a => Set UnbalancedSet a where
  empty = E

  insert x E           = T x E E
  insert x s@(T y _ _) = insert_aux y x s

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
        rbleft  :: { v:RedBlackSet {vv:a | vv < rbval} | ((color /= Red) || (getColor v /= Red))},
        rbright :: { v:RedBlackSet {vv:a | vv > rbval} | ((color /= Red) || (getColor v /= Red)) &&
                                                         (numBlack v) == (numBlack rbleft)}
      }
   @-}

{-@ predicate RedInvariant C S = (C /= Red) || (getColor S /= Red) @-}
{-@ predicate BlackInvariant S0 S1 = (numBlack S0) == (numBlack S1) @-}

data RedBlackSet a =
  Empty |
  Tree {
    color :: Color,
    rbval :: a,
    rbleft  :: RedBlackSet a,
    rbright :: RedBlackSet a
  }

testTree :: RedBlackSet Int
testTree = Tree Red 1 (Tree Black (-1) Empty (Tree Red (0) Empty Empty)) (Tree Black 2 Empty Empty)

{- Assuming that the number of black nodes along are paths to a leaf node are
 - equal, return this value. This function actually counts the number of black
 - nodes when recursing leftwards down the tree but, red black tree must have
 - this value be the same for all paths to a leaf node -}
{-@ measure numBlack @-}
{-@ numBlack :: RedBlackSet a -> Nat @-}
numBlack :: RedBlackSet a -> Int
numBlack Empty = 0
numBlack (Tree c _ l r) = (if c == Black then 1 else 0) + (numBlack l)

{-@ measure getColor @-}
{-@ getColor :: RedBlackSet a -> Color @-}
getColor Empty          = Black
getColor (Tree c _ _ _) = c

{-@ predicate IsGTrb N S = isEmptyrb S || N > (toprb S) @-}
{-@ predicate IsLTrb N S = isEmptyrb S || N < (toprb S) @-}

{-@ measure toprb @-}
{-@ toprb :: forall a. {v:RedBlackSet a | not (isEmptyrb v)} -> a @-}
toprb :: RedBlackSet a -> a
toprb (Tree _ v _ _) = v

{-@ measure isEmptyrb @-}
{-@ isEmptyrb :: v:RedBlackSet a -> {b:Bool | b <=> Set_emp (setElts  v)} @-}
isEmptyrb Empty = True
isEmptyrb _     = False

{-@ instance measure setElts :: forall a. RedBlackSet a -> Set.Set a
    setElts Empty         = (Set_empty 0)
    setElts (Tree _ v l r) = Set_cup (Set_sng v) (Set_cup (setElts l) (setElts r))
  @-}

{- Note about balance with respect to insert:
     balance is called after insert is recursivly called on one of the subtrees
     so, we know that the red invariant will hold for the other sub tree (it has
     not been changed). The black invariant will hold between the subtrees because
     insert only ever introduces a red node (empty case) or a black node to each
     subtree (when balancing) (this will probably be hard to prove to liquid).

     We do not know if the red invariant holds for the other subtree.

     The new precondition should say that the red invariant holds for at least
     one of the subtrees.
 -}

{- OK, I think I see what's going wrong here. Using the algorithm from the book,
 - the balance algorithm takes as arguments red black tree that do not need to
 - maintain the red-invariant. Using liquid, these trees cannot be represented in
 - the first place.
 -
 - I need to modify this function that that it takes some other structure that does
 - not enfore this invariant then, balance will construct from it a red black tree
 - after making sure the invariant holds
 -}

 {- When balance is called from inside insert, it is after inserting into either
  - the left or the right subtree (not both!). Importantly, you know which case
  - it is when calling balance. I plan to right two seperate functions for each case.
  -
  - In one case, I will assume that the invariants hold for the left subtree but,
  - the right subtree will not be a RedBlackSet. Instead, I will pass it as a 
  - 4-tuple of the arguments used to construct the tree. Hopefully, I'll be able
  - to massage these argumunts such that the invariants hold. For the other case,
  - I'll do the same thing but for the right subtree.
  -}

{-@ data NoRedInvariant a = NoRedInvariant {
        nricolor   :: Color,
        nrival   :: a,
        nrileft  :: RedBlackSet {vv:a | vv < nrival},
        nriright :: {v:RedBlackSet {vv:a | vv > nrival} |
          (nricolor /= Red || 
          (getColor nrileft) /= Red ||
          (getColor v) /= Red) &&
          (numBlack v) == (numBlack nrileft)}
      }
   @-}

data NoRedInvariant a = NoRedInvariant {
  nricolor :: Color,
  nrival :: a,
  nrileft :: RedBlackSet a,
  nriright :: RedBlackSet a
}

{-@ predicate NriRedInvariant Nri = (nricolor Nri) /= Red ||
                                    (getColor (nrileft Nri) /= Red &&
                                     getColor (nriright Nri) /= Red)
  @-}

{-@ instance measure setElts :: forall a. NoRedInvariant a -> Set.Set a
    setElts (NoRedInvariant _ v l r) = Set_cup (Set_sng v) (Set_cup (setElts l) (setElts r))
  @-}

{-@ measure nrinumBlack @-}
{-@ nrinumBlack :: NoRedInvariant a -> Nat @-}
nrinumBlack :: NoRedInvariant a -> Int
nrinumBlack (NoRedInvariant c _ l r) = (if c == Black then 1 else 0) + (numBlack l)

{-@ balanceLeft :: forall a. Ord a =>
      c:Color ->
      t:a ->

      l:{v:NoRedInvariant {vv:a | vv < t} | c == Red ==> NriRedInvariant v} ->

      r:{v:RedBlackSet {vv:a | vv > t} | RedInvariant c v &&
                                         (numBlack v) == (nrinumBlack l)} ->
      {v:NoRedInvariant a | (c /= Red ==> NriRedInvariant v) &&
                            (nrinumBlack v) == ( if c == Black then 1 else 0) + nrinumBlack l &&
                            (setElts v) == (Set_cup (Set_sng t) (Set_cup (setElts l) (setElts r)))}
  @-}
balanceLeft :: Ord a => Color -> a -> NoRedInvariant a -> RedBlackSet a -> NoRedInvariant a
balanceLeft Black z (NoRedInvariant Red y (Tree Red x a b) c) d =
  NoRedInvariant Red y (Tree Black x a b) (Tree Black z c d)

balanceLeft Black z (NoRedInvariant Red x a (Tree Red y b c)) d =
  NoRedInvariant Red y (Tree Black x a b) (Tree Black z c d)

balanceLeft c x (NoRedInvariant c' x' a' b' ) b =
  NoRedInvariant c x (Tree c' x' a' b') b

{-@ balanceRight :: forall a. Ord a =>
      c:Color ->
      t:a ->
      l:{v:RedBlackSet {vv:a | vv < t} | RedInvariant c v} ->

      r:{v:NoRedInvariant {vv:a | vv > t} | (c == Red ==> NriRedInvariant v) &&
                                            (nrinumBlack v) == (numBlack l)} ->

      {v:NoRedInvariant a | (c /= Red ==> NriRedInvariant v) &&
                            (nrinumBlack v) == ( if c == Black then 1 else 0) + numBlack l &&
                            (setElts v) == (Set_cup (Set_sng t) (Set_cup (setElts l) (setElts r)))}
   @-}
balanceRight :: Ord a => Color -> a -> RedBlackSet a -> NoRedInvariant a -> NoRedInvariant a
balanceRight Black x a (NoRedInvariant Red z (Tree Red y b c) d ) =
  NoRedInvariant Red y (Tree Black x a b) (Tree Black z c d)

balanceRight Black x a (NoRedInvariant Red y b (Tree Red z c d) ) =
  NoRedInvariant Red y (Tree Black x a b) (Tree Black z c d)

balanceRight c x a (NoRedInvariant c' x' a' b' ) =
  NoRedInvariant c x a (Tree c' x' a' b')

{-@ rb_insert_aux :: forall a. Ord a =>
      x:a ->
      s:RedBlackSet a ->
      {v:NoRedInvariant a | ((getColor s) /= Red ==> NriRedInvariant v) &&
                            (nrinumBlack v) == (numBlack s) &&
                            (setElts v) == (Set_cup (Set_sng x) (setElts s))}
  @-}
rb_insert_aux :: Ord a => a -> RedBlackSet a -> NoRedInvariant a
rb_insert_aux x Empty = NoRedInvariant Red x Empty Empty
rb_insert_aux x (Tree c y a b)
  | x < y     = balanceLeft c y (rb_insert_aux x a) b
  | x > y     = balanceRight c y a (rb_insert_aux x b)
  | otherwise = (NoRedInvariant c y a b)

instance Ord a => Set RedBlackSet a where
  empty = Empty

  insert x s = forceRedInvarient (rb_insert_aux x s)
    where forceRedInvarient (NoRedInvariant _ e a b) = Tree Black e a b

  member _ Empty = False
  member e (Tree _ x l r)
    | e < x     = member e l
    | e > x     = member e r
    | otherwise = True
