module Queue.Queue where

import Prelude hiding (head, tail)

import Data.Set
import qualified Data.Set.Internal

{- Note: I wanted to have len return Nat, liquid haskell did not recognize the
 - type. Nat is recognized elsewhere in this file, so this could be a problem
 - with LiquidHaskell but, I haven't spent much time looking into this. -}

{-@ class measure qlen  :: forall a. a -> {n:Int | n >= 0} @-}
{-@ class measure qelts :: forall a b. a b -> Data.Set.Internal.Set b @-}

{-@ class Queue q where
      empty   :: forall a.
        {q:(q a) | Set_emp (qelts q) &&
                   0 == qlen q}
      isEmpty :: forall a.
        q:(q a) -> {v:Bool | v <=> ((Set_emp (qelts q)) && 
                                    (0 == qlen q))}

      snoc    :: forall a.
        q0:q a -> e:a -> {q1:q a | (qelts q1) == Set_cup (Set_sng e) (qelts q0) &&
                                   (qlen q1) == (qlen q0) + 1}
      head    :: forall a.
        {q:q a | qlen q /= 0} -> {e:a | Set_mem e (qelts q)}

      tail    :: forall a.
        {q0:q a | qlen q0 /= 0} -> {q1:q a | (qlen q1) == (qlen q0) - 1}
  @-}

class Queue q where
  empty   :: q a
  isEmpty :: q a -> Bool

  snoc    :: q a -> a -> q a
  head    :: q a -> a
  tail    :: q a -> q a
