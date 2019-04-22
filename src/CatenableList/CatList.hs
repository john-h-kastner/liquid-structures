{-# LANGUAGE GADTs #-}

module CatList where

import Queue.Queue
import CatenableList.CatenableList

import Prelude hiding (head, tail, (++))

--{-@ data CatList q a =
--      E |
--      C
--        (element  :: a)
--        (children :: q (CatList q a))
--   @-}
        --(children :: {v:q (CatList q a) | qlen v /= 0})
        --(children :: {v:q ({vv:CatList q a | qlen vv /= 0}) | qlen v /= 0})
        --
        --
--data CatList q a = E | C a (q (CatList q a))


{-@ data CatList q a where
        E :: CatList q a
      | C :: a -> q (CatList q a) ->  CatList q a
  @-}
       
data CatList q a where
  E :: CatList q a
  C :: Queue q => a -> q (CatList q a) ->  CatList q a

{-@ measure test_len :: forall a. CatList q a -> Int 
    test_len E       = 0
    test_len (C _ q) = qlen q
  @-}


--{-@ link :: forall a q. Queue q =>
--     c0 : {v:CatList q a | qlen v /= 0} ->
--     c1 : {v:CatList q a | qlen v /= 0} ->
--     {v:CatList q a | qlen v  == (qlen c0) + (qlen c1)}
--  @-}
--link :: Queue q => CatList q a -> CatList q a -> CatList q a
--link (C x q) s = C x (q `snoc` s)
