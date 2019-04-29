{-# LANGUAGE MultiParamTypeClasses #-}
module Set.Set where

import qualified Data.Set as Set

{-@ class measure setElts :: forall s a. s a -> Set.Set a @-}

{-@ class Set s a where
      empty  :: {v:s a | Set_emp (setElts v)}
      insert :: e:a -> v:s a -> {vv: s a | (setElts vv) == Set_cup (Set_sng e) (setElts v)}
      member :: e:a -> v:s a -> {vv: Bool | vv <=> Set_mem e (setElts v)}
  @-}

class Set s a where
  empty  :: s a
  insert :: a -> s a -> s a
  member :: a -> s a -> Bool
