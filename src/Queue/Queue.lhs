\begin{code}
module Queue.Queue where

import Prelude hiding (head, tail)

{- Note: I wanted to have len return Nat, liquid haskell did not recognize the
 - type. Nat is recognized elsewhere in this file, so this could be a problem
 - with LiquidHaskell but, I haven't spent much time looking into this. -}

{-@ class measure qlen :: forall a. a -> {v:Int | v >= 0} @-}

{-@ class Queue q where
      empty   :: forall a.
        {q:(q a) | 0 == qlen q}
      isEmpty :: forall a.
        q:(q a) -> {v:Bool | v <=> (0 == qlen q)}

      snoc    :: forall a.
        q0:q a -> a -> {q1:q a | (qlen q1) == (qlen q0) + 1}
      head    :: forall a.
        {q:q a | qlen q /= 0} -> a
      tail    :: forall a.
        {q0:q a | qlen q0 /= 0} -> {q1:q a | (qlen q1) == (qlen q0) - 1}
  @-}

class Queue q where
  empty   :: q a
  isEmpty :: q a -> Bool

  snoc    :: q a -> a -> q a
  head    :: q a -> a

  tail    :: q a -> q a
\end{code}
