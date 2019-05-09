{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Queue.PhysicistsQueue where

import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (head, tail, reverse)
import qualified Prelude (tail)

import Queue.Queue

{- The inductive predicates did not work well with Haskell's built in lists so,
 - I've included a custom list datatype. -}
data List a = Nil | Cons a (List a)

{-@ measure llen @-}
{-@ llen :: List _ -> Nat @-}
llen :: List a -> Int
llen Nil = 0
llen (Cons _ t) = 1 + llen t

{-@ reflect app @-}
{-@ app ::
      l0:List a ->
      l1:List a ->
      {l2:List a | llen l2 == (llen l0 + llen l1)}
  @-}
app :: List a -> List a -> List a
app Nil l1        = l1
app (Cons h t) l1 = Cons h (app t l1)

{- This isn't tail recursive reverse because liquid was refusing to check that
 - version. It'd be nice to be able to use a tail recursive reverse but, this
 - is fine for now. -}
{-@ reflect reverse @-}
{-@ reverse ::
    l0:List a ->
    {l1:List a | llen l1 == llen l0}
  @-}
reverse :: List a -> List a
reverse Nil        = Nil
reverse (Cons h t) = app (reverse t) (Cons h Nil)

data PrefixP a where
  Prefix :: List a -> List a -> PrefixP a

data Prefix a where
  PrefixNil  :: List a -> Prefix a
  PrefixCons :: a -> List a -> List a -> Prefix a -> Prefix a

{-@ data Prefix a where
        PrefixNil  :: l:List a ->
                      Prop (Prefix Nil l)
      | PrefixCons :: h:a -> l0:List a -> l1:List a ->
                      Prop (Prefix l0 l1) ->
                      Prop (Prefix (Cons h l0) (Cons h l1))
  @-}

{-@ prefix_ex1 :: Prop (Prefix (Cons 1 Nil) (Cons 1 Nil)) @-}
prefix_ex1 :: Prefix Int
prefix_ex1 = PrefixCons 1 Nil Nil (PrefixNil Nil)

{-@ prefix_ex2 :: Prop (Prefix Nil Nil) @-}
prefix_ex2 :: Prefix Int
prefix_ex2 = PrefixNil Nil

{-@ prefix_ex3 :: Prop (Prefix (Cons 1  Nil) (Cons 1 (Cons 2 Nil))) @-}
prefix_ex3 :: Prefix Int
prefix_ex3 = PrefixCons 1 Nil (Cons 2 Nil) (PrefixNil (Cons 2 Nil))

{-@ lemma_prefixSelf :: forall a.
      l:List a ->
      Prop (Prefix l l)
  @-}
lemma_prefixSelf :: List a -> Prefix a
lemma_prefixSelf Nil        = PrefixNil Nil
lemma_prefixSelf (Cons h t) = PrefixCons h t t (lemma_prefixSelf t)

{-@ lemma_prefixApp :: forall a.
      l0 : List a -> l1 : List a -> l2 : List a ->
      Prop (Prefix l0 l1) ->
      Prop (Prefix l0 (app l1 l2))
  @-}
lemma_prefixApp :: List a -> List a -> List a -> Prefix a -> Prefix a
lemma_prefixApp _ l1 l2 (PrefixNil _) =
  PrefixNil (app l1 l2)
lemma_prefixApp l0 l1 l2 (PrefixCons h t0 t1 p) =
  PrefixCons h t0 (app t1 l2) (lemma_prefixApp t0 t1 l2 p)

{-@ lemma_prefixAppSelf :: forall a.
    l0 : List a -> l1 : List a ->
    Prop (Prefix l0 (app l0 l1))
  @-}
lemma_prefixAppSelf :: List a -> List a -> Prefix a
lemma_prefixAppSelf l0 l1 = lemma_prefixApp l0 l0 l1 (lemma_prefixSelf l0)

{-@ data PhysicistsQueue a = PQ {
      lenf :: Nat,
      f    :: {v:List a | llen v == lenf},
      lenr :: {v:Nat | v <= lenf},
      r    :: {v:List a | llen v == lenr},
      pre  :: {v:List a | (lenf /= 0 ==> llen v /= 0)},
      isPrefix :: Prop (Prefix pre f)
    }
  @-}

type PQ a = PhysicistsQueue a
data PhysicistsQueue a = PQ {
  lenf :: Int,
  f    :: List a,
  lenr :: Int,
  r    :: List a,
  pre  :: List a,
  isPrefix :: Prefix a
}

{-@ check :: forall a.
      lenf : Nat ->
      f    : {v:List a | llen v == lenf} ->
      lenr : Nat ->
      r    : {v:List a | llen v == lenr} ->
      pre  : List a ->
      isPrefix : Prop (Prefix pre f) ->
      {v:PQ a | qlen v == lenf + lenr}
   @-}
check :: Int -> List a -> Int -> List a -> List a -> Prefix a -> PQ a
check lenf f lenr r w p
  | lenr <= lenf = checkw lenf f lenr r w p
  | otherwise    = checkw (lenf + lenr) (app f (reverse r)) 0 Nil f (lemma_prefixAppSelf f (reverse r))

{-@ checkw :: forall a.
    lenf : Nat ->
    f    : {v:List a | llen v == lenf} ->
    lenr : {v:Nat | v <= lenf} ->
    r    : {v:List a | llen v == lenr} ->
    pre  : List a ->
    isPrefix : Prop (Prefix pre f) ->
    {v:PQ a | qlen v == lenf + lenr}
  @-}
checkw :: Int -> List a -> Int -> List a -> List a -> Prefix a -> PQ a
checkw lenf f lenr r Nil _ = PQ lenf f lenr r f (lemma_prefixSelf f)
checkw lenf f lenr r w  p  = PQ lenf f lenr r w p

instance Queue PhysicistsQueue where
  {-@ instance measure qlen :: PhysicistsQueue a -> Int
      qlen (PQ f _ r _ _ _) = f + r
    @-}

  empty = PQ 0 Nil 0 Nil Nil (PrefixNil Nil)
  
  isEmpty (PQ f _ _ _ _ _) = f == 0
  
  snoc (PQ lenf f lenr r w p) x = check lenf f (lenr + 1) (Cons x r) w p
  
  head (PQ _ _ _ _ (Cons x _) _) = x
  
  tail (PQ lenf (Cons _ f) lenr r (Cons _ w) (PrefixCons _ _ _ p)) =
    check (lenf - 1) f lenr r w p
