module Queue.BankersQueue where

{- DONE:
 -   lenf >= lenr is ensured
 -   saftey of partial functions is checked
 -}

{- TODO:
 -   content of queue is preserved
 -   queue order is presevered
 -   implement generic Queue typeclass
 -   write somee examples demonstrating checked properties
 -}

import Prelude hiding (head, tail)

{-@ data BankersQueue a = BQ {
      lenf :: Nat,
      f    :: {v:[a] | len v == lenf},
      lenr :: {v:Nat | v <= lenf},
      r    :: {v:[a] | len v == lenr}
    }
  @-}

data BankersQueue a = BQ {
  lenf :: Int,
  f    :: [a],
  lenr :: Int,
  r    :: [a]
} deriving Show

{-@ predicate OfSize Q N = (lenf Q) + (lenr Q) == N @-}

{-@ type BQ_NE a        = {q : BankersQueue a | not ( OfSize q 0) } @-}
{-@ type BQ_E a         = {q : BankersQueue a | OfSize q 0 } @-} 

{-@ check ::
    vlenf : Nat              ->
    {v:[_] | len v == vlenf} ->
    vlenr : Nat              ->                    
    {v:[_] | len v == vlenr} ->
    {q:BankersQueue _ | OfSize q (vlenf + vlenr)}
  @-}
check :: Int -> [a] -> Int -> [a] -> BankersQueue a
check lenf f lenr r =
  if lenr <= lenf then
    BQ lenf f lenr r
  else
    BQ (lenf + lenr) (f ++ (reverse r)) 0 []

{-@ empty :: BQ_E _ @-}
empty :: BankersQueue a
empty = BQ 0 [] 0 []

{-@ isEmpty :: q:BankersQueue _ -> {b:Bool | b <=> OfSize q 0} @-}
isEmpty :: BankersQueue a -> Bool
isEmpty (BQ lenf f lenr r) = (lenf == 0)

{-@ snoc :: forall a.
    q : BankersQueue a ->
    e : a              ->
    {q' : BankersQueue a | (lenf q') + (lenr q') == (lenf q) + (lenr q) + 1}
  @-}
snoc :: BankersQueue a -> a -> BankersQueue a
snoc (BQ lenf f lenr r) x = check lenf f (lenr + 1) (x : r)

{-@ head :: forall a.
    q : BQ_NE a ->
    a
  @-}
head :: BankersQueue a -> a
head (BQ lenf (x : f') lenr r) = x

{-@ tail :: forall a.
    q : BQ_NE a ->
    {q' : BankersQueue a | (lenf q') + (lenr q') == (lenf q) + (lenr q) - 1}
  @-}
tail (BQ lenf (x : f') lenr r) = check (lenf - 1) f' lenr r
