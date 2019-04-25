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

# Random-Access Lists

A random-access list as presented in *Purely Functional Data Structures* is an
extension of the usual cons-list that supports lookup and update functions like
those you would expect to see for a traditional array. While for a queue it
sufficed to know that the structure was not empty before retrieving the next
element, a random access list must verify that a requested index is with the
bounds of the list before any lookup or update operation. This requirement is
encoded in the refinement types for these functions.

The interface used for random access list is given below and is also available
in the [relevant source file](src/RandomAccessList/RandomAccessList.hs).

```haskell
{-@ class measure rlen :: forall a. a -> {v:Int | v >= 0} @-}
{-@ class RandomAccessList r where
      empty   :: forall a.
        {r:(r a) | 0 == rlen r}
      isEmpty :: forall a.
        r:(r a) -> {v:Bool | v <=> (0 == rlen r)}

      cons    :: forall a.
        a -> r0:r a -> {r1:r a | (rlen r1) == (rlen r0) + 1}
      head    :: forall a.
        {r:r a | rlen r /= 0} -> a
      tail    :: forall a.
        {r0:r a | rlen r0 /= 0} -> {r1:r a | (rlen r1) == (rlen r0) - 1}

      lookup :: forall a.
        r:r a -> {i:Nat | i < rlen r} -> a
      update :: forall a.
        r0:r a -> {i:Nat | i < rlen r0} -> a -> {r1:r a | (rlen r1) == (rlen r1)}
  @-}
```

## [Simple Random-Access List](src/RandomAccessList/SimpleRandomAccessList.hs)

This implementation is not one given in the book. It is a very simple implementation
that I wrote to practice using LiquidHaskell and to quickly check that the
refinement types I wrote for the `RandomAccessList` type class were reasonable.

The data type used for this implementation is a wrapper around Haskells List type
and the functions are implemented as operations on the internal list. No additional
refinements are given to the constructor as there are no invariants that must be
maintained.

```haskell
data SimpleRandomAccessList a = SRAL [a]
```

[1]: http://www.cs.cmu.edu/~rwh/theses/okasaki.pdf
[2]: https://ucsd-progsys.github.io/liquidhaskell-blog/
[3]: https://ucsd-progsys.github.io/liquidhaskell-blog/2016/09/18/refinement-reflection.lhs/
[4]: http://ucsd-progsys.github.io/liquidhaskell-tutorial/09-case-study-lazy-queues.html
