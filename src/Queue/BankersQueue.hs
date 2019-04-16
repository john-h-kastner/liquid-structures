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

{-@ measure qlen @-}
qlen :: BankersQueue a -> Int
qlen (BQ f _ r _) = f + r

{-@ check ::
    vlenf : Nat              ->
    {v:[_] | len v == vlenf} ->
    vlenr : Nat              ->                    
    {v:[_] | len v == vlenr} ->
    {q:BankersQueue _ | qlen q == (vlenf + vlenr)}
  @-}
check :: Int -> [a] -> Int -> [a] -> BankersQueue a
check lenf f lenr r =
  if lenr <= lenf then
    BQ lenf f lenr r
  else
    BQ (lenf + lenr) (f ++ (reverse r)) 0 []

{-@ empty :: {q:BankersQueue _ | qlen q == 0} @-}
empty :: BankersQueue a
empty = BQ 0 [] 0 []

{-@ isEmpty :: q:BankersQueue _ -> {b:Bool | b <=> qlen q == 0} @-}
isEmpty :: BankersQueue a -> Bool
isEmpty (BQ lenf f lenr r) = (lenf == 0)

{-@ snoc :: forall a.
    q : BankersQueue a ->
    e : a              ->
    {q' : BankersQueue a | qlen q' == (qlen q) + 1}
  @-}
snoc :: BankersQueue a -> a -> BankersQueue a
snoc (BQ lenf f lenr r) x = check lenf f (lenr + 1) (x : r)

{-@ head :: forall a.
    {q : BankersQueue a | qlen q /= 0} ->
    a
  @-}
head :: BankersQueue a -> a
head (BQ lenf (x : f') lenr r) = x

{-@ tail :: forall a.
    {q : BankersQueue a | qlen q /= 0} ->
    {q' : BankersQueue a | qlen q' == (qlen q) - 1}
  @-}
tail (BQ lenf (x : f') lenr r) = check (lenf - 1) f' lenr r
