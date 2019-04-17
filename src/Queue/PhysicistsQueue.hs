module Queue.PhysicistsQueue where

import Prelude hiding (head, tail)
import qualified Prelude (tail)

import Queue.Queue

{- TODO: ensure pre is a prefix of f. For now, I only check that the pre is
 - shorter than f and that it's elements are a subset of f's elements. Just
 - kidding, I'm not doing the set thing either.
 -
 - I would like to ensure a subset property like:
 -
 -     pre  :: {v:[a] |
 -       Set_sub (listElts v) (listElts f) &&
 -       len v <= lenf &&
 -       (lenf /= 0 ==> len v /= 0)}
 -
 - Even better is a prefix relation like:
 -
 -     pre :: {v:[a] |
 -       Prefix v f &&
 -       len v <= lenf &&
 -       (lenf /= 0 ==> len v /= 0)}
 -
 - In think that the subset relation should be doable but, I have not been
 - able to figure it out in the time I've spent so far. The issue I encountered
 - was that (l0 <= l1) =/=> (tl 0) <= (tl 1).
 -
 -     Counterexample:
 -       let l0 = [1, 2] and l1 = [2, 1]
 -       l0 <= l1 but,
 -       (tl l0) = [2]
 -       (tl l1) = [1]
 -       [2] </= [1]
 -
 - To implement the prefix relation, I think I can either use coq style inductive
 - predicates (these do seem to exists in LiquidHaskell) or, write a recursive
 - prefix test function and raise it to the refinement type level using reflection.
 - I have not attempted either of these approaches.
 -}

{-@ data PhysicistsQueue a = PQ {
      lenf :: Nat,
      f    :: {v:[a] | len v == lenf},
      lenr :: {v:Nat | v <= lenf},
      r    :: {v:[a] | len v == lenr},
      pre  :: {v:[a] | len v <= lenf && (lenf /= 0 ==> len v /= 0)}
    }
  @-}

type PQ a = PhysicistsQueue a
data PhysicistsQueue a = PQ {
  lenf :: Int,
  f    :: [a],
  lenr :: Int,
  r    :: [a],
  pre  :: [a]
}

{-@ check :: forall a.
      lenf : Nat ->
      f    : {v:[a] | len v == lenf} ->
      lenr : Nat ->
      r    : {v:[a] | len v == lenr} ->
      pre  : {v:[a] | len v <= lenf} ->
      {v:PQ a | qlen v == lenf + lenr}
   @-}
check :: Int -> [a] -> Int -> [a] -> [a] -> PQ a
check lenf f lenr r w
  | lenr <= lenf = checkw lenf f lenr r w
  | otherwise    = checkw (lenf + lenr) (f ++ reverse r) 0 [] f
    where
      {-@ checkw :: forall a.
            lenf : Nat ->
            f    : {v:[a] | len v == lenf} ->
            lenr : {v:Nat | v <= lenf} ->
            r    : {v:[a] | len v == lenr} ->
            pre  : {v:[a] | len v <= lenf} ->
            {v:PQ a | qlen v == lenf + lenr}
        @-}
      checkw :: Int -> [a] -> Int -> [a] -> [a] -> PQ a
      checkw lenf f lenr r [] = PQ lenf f lenr r f
      checkw lenf f lenr r w  = PQ lenf f lenr r w

{- I needed this append function for an attempt at ensuring the prefix relationship
 - between f and w. That attempt never made it far enough to get a commit so,
 - I'm leaving this for the time being. It should be removed if I ever get the
 - prefix invariant working properly. -}
{-
      {- Prelude.++ was not providing the set element property I needed so, I
       - provide my own implementation. I might be able to just write a lemma
       - to avoid reimplementing the entire function -}
      {-@ append :: forall a.
            xs : [a] ->
            ys : [a] ->
            {v:[a] | (len v)      == ((len xs) + (len ys)) &&
                     (listElts v) == (Set_cup (listElts xs) (listElts ys))}
        @-}
      append :: [a] -> [a] -> [a]
      append xs []     = xs
      append [] ys     = ys
      append (x:xs) ys = x : (append xs ys)
-}

instance Queue PhysicistsQueue where
  {-@ instance measure qlen :: PQ a -> Int
      qlen (PQ f _ r _ _) = f + r
    @-}

  empty                         = PQ 0 [] 0 [] []
  isEmpty (PQ f _ _ _ _)        = f == 0

  snoc (PQ lenf f lenr r w) x   = check lenf f (lenr + 1) (x:r) w
  head (PQ _ _ _ _ (x:_))       = x
  {- I don't know why Okasaki used Prelude.tail here instead of pattern matching.
   - I've left it the same as his implementation. -}
  tail (PQ lenf f lenr r w) = check (lenf - 1) (Prelude.tail f) lenr r (Prelude.tail w)
