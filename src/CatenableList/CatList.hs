{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--ple-local" @-}

module CatList where

import Queue.Queue
import Queue.BankersQueue
import CatenableList.CatenableList

import Prelude hiding (head, tail, (++))

{- I was having a lot of trouble convincing liquid to work over an arbitrary queue
 - implementation so, I've specialized this to only use the BankersQueue. Okasaki's
 - original implementation could use anything from the Queue typeclass. -}

{-@ data CatList a =
      E |
      C
        (element  :: a)
        (children :: BQ (CatList a))
   @-}
        --(children :: {v:BQ ({vv:CatList a | test_len vv > 0}) | qlen v > 0})

data CatList a = E | C a (BQ (CatList a))

{-@ measure test_len :: forall a. CatList a -> Nat 
    test_len E       = 0
    test_len (C _ q) = 1 + (sum_len (toList q))
  @-}

{-@ measure sum_len :: forall a. MList (CatList a) -> Nat
    sum_len Nil        = 0
    sum_len (Cons h t) = (test_len h) + (sum_len t)
  @-}


--{-@ link :: forall a.
--     c0 : {v:CatList a | test_len v > 0} ->
--     c1 : {v:CatList a | test_len v > 0} ->
--     CatList a
--  @-}
--link :: CatList a -> CatList a -> CatList a
--link (C x q) s = C x (q `snoc` s)

data MList a = Nil | Cons (CatList a) (MList a)

{-@ reflect mListOfList @-}
mListOfList []    = Nil
mListOfList (h:t) = Cons h (mListOfList t)

{-@ reflect reverse' @-}
reverse' Nil         = Nil
reverse' (Cons x xs) = append (reverse' xs) (Cons x Nil)

{-@ reflect append @-}
append Nil ys         = ys
append (Cons x xs) ys = Cons x (append xs ys)

{-@ reflect toList @-}
toList (BQ _ f _ r ) = append (mListOfList f) (reverse' (mListOfList r))
