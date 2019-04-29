module RandomAccessList.SimpleRandomAccessList where

import Prelude hiding (head, tail, lookup)

import RandomAccessList.RandomAccessList

{- This module is a very basic implementation of the RandomAccessList interface.
 - It's a place holder so that there's some implementation here until I figure
 - out the more advanced version in the book
 -
 - Yes, this is just a list. It doesn't get much simpler than that. The point
 - of this module is that I'll actualy be able to verfiy it.
 -
 - Liquid doesn't seem to play nice with newtype so, I'm using data instead -}
type SRAL a = SimpleRandomAccessList a
data SimpleRandomAccessList a = SRAL [a]

instance RandomAccessList SimpleRandomAccessList where
  {-@ instance measure rlen :: SRAL a -> {v:Int | v >= 0}
       rlen (SRAL l) = len l
    @-}

  empty = SRAL []
  isEmpty (SRAL []) = True
  isEmpty _        = False

  cons h (SRAL t) = SRAL (h:t)

  head (SRAL (h:_)) = h
  tail (SRAL (_:t)) = SRAL t

  lookup l 0 = head l
  lookup l i = lookup l (i - 1)

  update l 0 e = e      `cons` tail l
  update l i e = head l `cons` update (tail l) (i - 1) e
