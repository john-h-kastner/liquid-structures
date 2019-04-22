module CatenableList.CatenableList where

import Prelude hiding (head, tail, (++))

import Queue.Queue

{- TODO: add class law for associative append -}

{-@ class Queue c => CatenableList c where
      cons    :: forall a.
        a -> c0:c a -> {c1:c a | (qlen c1) == (qlen c0) + 1}

      (++)    :: forall a.
        c0:c a -> c1:c a -> {c2:c a | (qlen c1) == (qlen c0) + (qlen c1)}
  @-}

class Queue c => CatenableList c where
  cons    :: a -> c a -> c a
  (++)    :: c a -> c a -> c a
