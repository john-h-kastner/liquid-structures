\begin{code}
module Queue.Queue where

import Prelude hiding (head, tail)
\end{code}

= Introduction

The first and perhaps simplest abstract data type presented in the book is the
first-in-first-out queue. In this file, a type class is declared that specifies
the functions that must be provided by all queues.

= Queue Interface

\begin{code}
{-@ class Queue q where
\end{code}

The first two functions deal with empty queues. The first is used to obtain an
empty queue while the second is used to test if a queue is empty. Both have
refinement types specifying that an empty queue has length equal to zero.

\begin{code}
      empty   :: forall a.
        {q:(q a) | 0 == qlen q}
      isEmpty :: forall a.
        q:(q a) -> {v:Bool | v <=> (0 == qlen q)}
\end{code}

The next function, `snoc` - `cons` backwards , is the primary constructor for a
queue. It is used to add an element to the end of the queue. Since this operation
should increase the length of a queue by one, the refinement type specifies that
the length of the returned queue, `q1` is one more than the length of the original
queue, `q0`.

\begin{code}
      snoc    :: forall a.
        q0:q a -> a -> {q1:q a | (qlen q1) == (qlen q0) + 1}
\end{code}

After constructing the queue, the most common operation done on the queue will
be reading and removing the head. These operation are provided by `head` and `tail`
respectively. Both functions have an interesting refinement on the input queue -
it cannot be empty. Since taking the head or tail of an empty queue would result
in a run time error, this refinement ensures that liquid can verify that no such
function calls happen.

\begin{code}
      head    :: forall a.
        {q:q a | qlen q /= 0} -> a
      tail    :: forall a.
        {q0:q a | qlen q0 /= 0} -> {q1:q a | (qlen q1) == (qlen q0) - 1}
  @-}
\end{code}

== Measures

For each queue function, there was some refinement specified about the length
of the queue. Since there isn't a notion of length for arbitrary types, each
queue will also need to specify how length should be calculated. This is done
with a `class measure`.

\begin{code}
{-@ class measure qlen :: forall a. a -> {v:Int | v >= 0} @-}
\end{code}

<details>
<summery> Haskell declaration </summery>
\begin{code}
class Queue q where
  empty   :: q a
  isEmpty :: q a -> Bool

  snoc    :: q a -> a -> q a
  head    :: q a -> a
  tail    :: q a -> q a
\end{code}
</details>
