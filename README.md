# liquid-structures

This project contains Haskell implementations of data structures from Chris
Okasaki's Book [Purely Functional Data Structures][1] with invariants statically
checked using [LiquidHaskell][2]. The implementations are based on the those
provided in the appendix of Okasaki's book but, in many cases they have been
modified to facilitate the addition of refinement types. Beyond simply ensuring
invariants, this project also attempts to use LiquidHaskell as a
[theorem prover][3] to prove other interesting properties.

# Queues 

The first and perhaps simplest abstract data type presented in the book is the
first-in-first-out queue. The first queue implementation, the batched queue, is
used as a [case study][4] in the LiquidHaskell tutorial, so I have opted not to
reproduce it here. I have included two similar queues: the banker's and physicist's
queue. 

The interface implemented by each queue is given below or, you can view it in
full in [its source file](src/Queue/Queue.hs).

```haskell
{-@ class measure qlen :: forall a. a -> Int @-}
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
```

## [Banker's Queue](src/Queue/BankersQueue.hs)

```haskell
{-@ data BankersQueue a = BQ {
      lenf :: Nat,
      f    :: {v:[a] | len v == lenf},
      lenr :: {v:Nat | v <= lenf},
      r    :: {v:[a] | len v == lenr}
    }
  @-}
```

The banker's queue is designed to enable using the banker's method for analysing 
amortized cost in a lazy data structure. To this end, for each of the two lists
it maintains a count of the number of elements in the list with the invariant
that the rear (second) list must be non longer than the front (first) list. This
is the primary property that is checked by LiquidHaskell.

## [Physicist's Queue](src/Queue/PhysicistsQueue.hs)

```haskell   
{-@ data PhysicistsQueue a = PQ {
      lenf :: Nat,
      f    :: {v:[a] | len v == lenf},
      lenr :: {v:Nat | v <= lenf},
      r    :: {v:[a] | len v == lenr},
      pre  :: {v:[a] | len v <= lenf && (lenf /= 0 ==> len v /= 0)}
    }
  @-}
```

The physicist's queue is similar in structure to the banker's queue but, it is
instead designed for analysis using the physicist's method. The data structure
maintains the same front and rear lists as the bankers queue with the same
constraints but, it also maintains a prefix lists that must be a prefix of the
front list.

The refinement types for this data structure should ensure this invariant but,
at the moment they only ensure that the prefix list is shorter than the front
list and that the list is nonempty when the front list is nonempty. Hopefully
this will be fixed before I am finished with this project.

[1]: http://www.cs.cmu.edu/~rwh/theses/okasaki.pdf
[2]: https://ucsd-progsys.github.io/liquidhaskell-blog/
[3]: https://ucsd-progsys.github.io/liquidhaskell-blog/2016/09/18/refinement-reflection.lhs/
[4]: http://ucsd-progsys.github.io/liquidhaskell-tutorial/09-case-study-lazy-queues.html
