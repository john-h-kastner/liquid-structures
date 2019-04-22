module Queue.BankersQueue where

{- DONE:
 -   lenf >= lenr is ensured
 -   saftey of partial functions is checked
 -   implement generic Queue typeclass
 -}

{- TODO:
 -   content of queue is preserved
 -   queue order is presevered
 -   write some examples demonstrating checked properties
 -}

import Prelude hiding (head, tail)

import Queue.Queue

{-@ data BankersQueue a = BQ {
      lenf :: Nat,
      f    :: {v:[a] | len v == lenf},
      lenr :: {v:Nat | v <= lenf},
      r    :: {v:[a] | len v == lenr}
    }
  @-}

type BQ a = BankersQueue a
data BankersQueue a = BQ {
  lenf :: Int,
  f    :: [a],
  lenr :: Int,
  r    :: [a]
} deriving Show

{-@ check ::
    vlenf : Nat              ->
    {v:[_] | len v == vlenf} ->
    vlenr : Nat              ->                    
    {v:[_] | len v == vlenr} ->
    {q:BQ _ | qlen q == (vlenf + vlenr)}
  @-}
check :: Int -> [a] -> Int -> [a] -> BQ a
check lenf f lenr r =
  if lenr <= lenf then
    BQ lenf f lenr r
  else
    BQ (lenf + lenr) (f ++ (reverse r)) 0 []

{-@ instance measure qhead :: BQ a -> a @-}
{-@ ignore qhead @-}
qhead bq = head

{-@ instance measure qtail :: BQ a -> BQ a @-}
{-@ ignore qtail @-}
qtail bq = tail
 
instance Queue BankersQueue where
  {-@ instance measure qlen :: BQ a -> {v:Int | v >= 0}
      qlen (BQ f _ r _) = f + r
    @-}

  empty = BQ 0 [] 0 []
  isEmpty (BQ lenf f lenr r) = (lenf == 0)

  snoc (BQ lenf f lenr r) x = check lenf f (lenr + 1) (x : r)
  head (BQ lenf (x : f') lenr r) = x
  tail (BQ lenf (x : f') lenr r) = check (lenf - 1) f' lenr r
