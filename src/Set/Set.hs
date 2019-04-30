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
 - BEGIN Implementation
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
