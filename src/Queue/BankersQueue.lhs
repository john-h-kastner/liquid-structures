\begin{code}
module Queue.BankersQueue where

import Prelude hiding (head, tail)
\end{code}

= Introduction

The bankers queue is an implementation of the queue abstract data type so, we
will need to import the type class declared in `Queue.lhs`.

\begin{code}
import Queue.Queue
\end{code}

The banker's queue is designed to enable using the banker's method for analysing
amortized cost in a lazy data structure. Two lists are maintained in the
data structure. The first is some prefix of the queue while the second is the
remaining suffix of the queue. The primary invariant is that the prefix list
cannot be shorter than the suffix list.

This queue is used as a [case study][1] in the LiquidHaskell tutorial, but I have
independently reproduced it here.

= Data structure declaration

The invariants mentioned in the introduction are formally specified in the declaration
of the `BankersQueue` data structure. 

\begin{code}
{-@ data BankersQueue a = BQ {
\end{code}

The first list is some prefix of the queue and it has some length that is stored
in the `BankersQueue` data structure. The refinement `len v == lenf` ensures that
the stored length is equal to the actual length of the list.

\begin{code}
      lenf :: Nat,
      f    :: {v:[a] | len v == lenf},
\end{code}

The second list in the data structure is the remaining suffix of the queue. As
with the prefix list, the length of the list is stored and there is a refinement
to ensure that this matches the real length. This list also has a more interesting
refinement that ensures the primary bankers queue invariant. The length of the
suffix list must be less than or equal to the length of the prefix list. This
is accomplished by the refinement on `lenr`.

\begin{code}
      lenr :: {v:Nat | v <= lenf},
      r    :: {v:[a] | len v == lenr}
    }
  @-}
\end{code}

<details>
<summary>Haskell declaration</summary>
\begin{code}
type BQ a = BankersQueue a
data BankersQueue a = BQ {
  lenf :: Int,
  f    :: [a],
  lenr :: Int,
  r    :: [a]
} deriving Show
\end{code}
</details>

== Catching a Violated Invariant

This refined definition of the banker's queue is enough for LiquidHaskell to
automatically detect some errors. Consider the following (incorrect) implementation
of `snoc`.

```haskell
snoc (BQ lenf f lenr r) x = BQ lenf f (lenr+1) (x:r)
```        

This implementation always adds the new item on to the suffix list. Using the
standard Haskell type checker, this would not raise any errors but, it clearly
does not maintain the bankers queue invariant. At some point, the suffix list
will become longer than the prefix list.

Running LiquidHaskell on this implementation, on the other hand, will raise
an error. LiquidHaskell is able to determine that the invariant does not always
hold.

```
165 | snoc (BQ lenf f lenr r) x = BQ lenf f (lenr+1) (x:r)
                                             ^^^^^^^^
  Inferred type
    VV : {v : GHC.Types.Int | v == lenr + 1}

  not a subtype of Required type
    VV : {VV : GHC.Types.Int | VV >= 0
                               && VV <= lenf}
```

= Smart Constructor

Before moving on to the real implementations for queue functions, it will be
useful to define an easy way to make sure that the banker's queue invariant holds.
This will be a function with the same type as the standard constructor but with
a stronger refinement type.

The refinement type for the bankers queue constructor is derived from the data
declaration in the same way that the Haskell type of the constructor is derived.
Below is the (abbreviated) refinement type.

```haskell
lenf : {v : Int | v >= 0} ->
f    : {v : [a] | len v == lenf} ->
lenr : {v : Int | v >= 0 && v <= lenf} ->
r    : {v : [a] | len v == lenr} ->
{q : BankersQueue a | qlen q == lenf + lenr}
```

The refinement type of the smart constructor will weaken refinements on the
parameters while providing the same refinement for the return value

\begin{code}
check :: Int -> [a] -> Int -> [a] -> BQ a
{-@ check ::
    vlenf : Nat              ->
    {v:[_] | len v == vlenf} ->
\end{code}

The first two parameters were identical but, `vlenr` does not need to be less
than or equal to `vlenf`. In the case it is greater, the smart constructor will
rearrange the data so that this invariant ultimately is true.

\begin{code}
    vlenr : Nat              ->                    
    {v:[_] | len v == vlenr} ->
    {q:BQ _ | qlen q == (vlenf + vlenr)}
  @-}
\end{code}

Given the refinement type, writing the function is simple. There are two cases:

\begin{code}
check lenf f lenr r =
\end{code}

* Case 1: The invariant holds. In this case, there is nothing to do so, the
  constructor is called immediately.

\begin{code}
  if lenr <= lenf then
    BQ lenf f lenr r
\end{code}

* Case 2: The invariant does not hold. The data must be manipulated so that is
does hold. The simplest way to do this is to replace the suffix list with an
empty list. Once this is done, the prefix list should be append with the revered
suffix list to preserve the contents and the order of the queue. Note that
neither the contents nor the order of the queue is checked by LiquidHaskell.

\begin{code}
  else
    BQ (lenf + lenr) (f ++ (reverse r)) 0 []
\end{code}

= Implementing the type class

The first two sections showed how to bankers queue invariant is checked (the
constructor) and how the invariant is restored in unstructured data (the smart
constructor). With these tools, the `Queue` type class can be implemented in a
way that ensures all of the refinements introduced by the declaration in `Queue.lhs`
alongside the invariants specific to the bankers queue introduced in this file.

\begin{code}
instance Queue BankersQueue where
\end{code}

The simplest thing to do is implementing the length measure since it doesn't have
to worry about the invariants. The length of the whole queue is the sum of the
prefix length and the suffix length.

\begin{code}
  {-@ instance measure qlen :: BQ a -> Int
      qlen (BQ f _ r _) = f + r
    @-}
\end{code}

Creating an empty queue is trivial because the length of an empty list will
be less than or equal to the length of another empty list. It is not necessary
to call the smart constructor but, it could be used in place of the standard
constructor.

\begin{code}
  empty = BQ 0 [] 0 []
\end{code}

`isEmpty` is just as simple as `empty`. A banker's queue is empty if it's prefix
list is empty. The length of the suffix list is not relevant because the only
suffix list that maintains the invariant is another empty list.

\begin{code}
  isEmpty (BQ lenf f lenr r) = (lenf == 0)
\end{code}

Again, `head` is a very simple function. The head of the list is the first element
of the prefix list. Based on the refinement on `Queue.lhs` LiquidHaskell will
check that `head` is total for all non empty queues. Since the suffix list can't
be non-empty if the prefix list is empty, if there are any elements in the queue
there will be at least on element in the prefix queue.

\begin{code}
  head (BQ lenf (x : f') lenr r) = x
\end{code}

`snoc` and `tail` are the interesting functions because they need to manipulate
the lists in the queue. After manipulating the lists, the invariant does not
necessarily hold so, the functions need to call the smart constructor instead
of the standard constructor. Since the smart constructor ensures that the bankers
queue invariant holds for the return value, the functions do not need to do any
other work.

\begin{code}
  snoc (BQ lenf f lenr r) x = check lenf f (lenr + 1) (x : r)
\end{code}

`tail` has one concerns that is not relevant to `snoc`: it is not defined for
queues with an empty prefix list. The same reasoning as `head` applies here,
the refinement in `Queue.lhs` ensures that this will not happen.

\begin{code}
  tail (BQ lenf (x : f') lenr r) = check (lenf - 1) f' lenr r
\end{code}

[1]: http://ucsd-progsys.github.io/liquidhaskell-tutorial/09-case-study-lazy-queues.html
