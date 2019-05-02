# liquid-structures

This project contains Haskell implementations of data structures from Chris
Okasaki's Book [Purely Functional Data Structures][1] with invariants statically
checked using [LiquidHaskell][2]. The implementations are based on the those
provided in the appendix of Okasaki's book but, in many cases they have been
modified to facilitate the addition of refinement types. There are also some
structures that were not taken from the book. These tend to be simpler structures
used to experiment with and learn LiquidHaskell.  Beyond simply ensuring
invariants, this project also attempts to use LiquidHaskell as a
[theorem prover][3] to prove other interesting properties.

# [Queues](src/Queue/Queue.hs)

The first and perhaps simplest abstract data type presented in the book is the
first-in-first-out queue. The first queue implementation, the batched queue, is
used as a [case study][4] in the LiquidHaskell tutorial, so I have opted not to
reproduce it here. I have included two similar queues: the banker's and physicist's
queue.

The interface implemented by each concrete queue provides functions for adding
to the end, reading and removing from the front, obtaining an empty queue and
testing if a given queue is empty. The refinement types for these functions are
used to track the length of a queue and to ensure that `head` and `tail` are
never called on empty queues.

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

The banker's queue is designed to enable using the banker's method for analysing
amortized cost in a lazy data structure. Two lists are maintained in the
data structure. The first is some prefix of the queue while the second is the
remaining suffix of the queue. The primary invariant is that the prefix list
cannot be shorter than the suffix list. This is checked by LiquidHaskell
according to the following refinement type for the queue constructor.

```haskell
{-@ data BankersQueue a = BQ {
      lenf :: Nat,
      f    :: {v:[a] | len v == lenf},
      lenr :: {v:Nat | v <= lenf},
      r    :: {v:[a] | len v == lenr}
    }
  @-}
```

## [Physicist's Queue](src/Queue/PhysicistsQueue.hs)

The physicist's queue is similar in structure to the banker's queue but, it is
instead designed for analysis using the physicist's method. The data structure
maintains the same prefix and suffix lists as the bankers queue with the same
constraints but, it also maintains a second prefix lists that must be a prefix
of the original prefix list.

The refinement types for this data structure should ensure this invariant but,
at the moment they only ensure that the new prefix list is shorter than the original
prefix list and that it is nonempty when the original list is nonempty. Hopefully
this will be fixed before I am finished with this project.

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

# [Sets](src/Set/Set.hs)

Okasaki's book presents a very simple interface for sets. Only insertion and a
membership predicate are required. This could, of course, be extended to support
other common functions over sets.

The refinement types for `empty` and `insert` encode these operations in terms
of functions understood by LiquidHaskell's SMT solver. At the moment, the type
of member is not refined.

```haskell
{-@ class Set s a where
      empty  ::
        {v:s a | Set_emp (setElts v)}
      insert ::
        e:a -> v:s a -> {vv: s a | (setElts vv) == Set_cup (Set_sng e) (setElts v)}
      member ::
        e:a -> v:s a -> Bool
  @-}
```

I want to ensure that member returns true if and only if the element is in the
set. Writing a refinement type that encodes this property is simple but, I have
not been able to write a set implementation that checks using such a refinement type.

```haskell
member :: e:a -> v:s a -> {b:Bool | b <=> Set_mem e (setElts b)}
```

## [Unbalanced Set](src/Set/Set.hs)

Unbalanced set implements the set interface using an unbalanced binary search
tree. Since it is a binary search tree, the invariant checked in the constructor
should be that the value at an interior node is greater than the value at its
left child and less than the value at its right child.

This is accomplished using predicates `IsGT` and `IsLT`. These predicates first
check that a tree is not empty then they retrieve the value and the node so that
it can be compared against some other value.

```haskell
{-@ data UnbalancedSet a =
      E |
      T {
        val   :: a,
        left  :: {v : UnbalancedSet a | IsGT val v},
        right :: {v : UnbalancedSet a | IsLT val v}
      }
@-}

{-@ predicate IsGT N S = isEmpty S || N > (usTop S) @-}
{-@ predicate IsLT N S = isEmpty S || N < (usTop S) @-}
```

# [Heaps](src/Heap/Heap.hs)

The refinement types for the `Heap` typeclass would ideally track the size of
a heap and provide some guarantee that the element returned by `findMin` is, in
fact, the smallest element in the heap. The current refinements only protect
against calling `findMin` and `deleteMin` on empty heaps Individual heap
implementations introduce their own invariants for that ensure that the minimum
element is kept at the top.

Due to issues working with LiquidHaskell, none of the heap implementations are
actually instances of this typeclass. The functions of the typeclass are
implemented by each heap and, the same refinement types are applied to the
implementations but, I have not been able to able to write them as a formal
instance of the `Heap` typeclass. The interface below is what should be
implemented when this problem is resolved.

```haskell
{-@ class Heap h where
      empty     :: forall a. Ord a =>
        {h:h a | 0 == hsize h}
      isEmpty   :: forall a. Ord a =>
        h:h a -> {v:Bool | v <=> (0 == hsize h)}

      insert    :: forall a. Ord a =>
        a -> h0:h a -> {h1:h a | (hsize h1) == (hsize h0) + 1}
      merge     :: forall a. Ord a =>
        h0:h a -> h1:h a -> {h2:h a | (hsize h2) == (hsize h0) + (hsize h1)}

      findMin   :: forall a. Ord a =>
        {h:h a | hsize h /= 0} -> a
      deleteMin :: forall a. Ord a =>
        {h0:h a | hsize h0 /= 0} -> {h1: h a | (hsize h1) == (hsize h0) - 1}
  @-}
```

## [Sorted List Heap](src/Heap/SortedListHeap.hs)

The Sorted List Heap is a trivial implementation of a heap not take from *Purely
Functional Data Structures* that keeps track of the smallest element by
maintaining a sorted list. Of course, this is not a particularly efficient
implementation (it has linear time insertion rather than logarithmic) but,
writing refinement types to force an ordered list is slightly easier than doing
the same for any of the tree based heap implementations.

The property ensured for this data structure is that for list larger than the
singleton list the head of the list is at least as small as the head of the tail.
This property is then recursively checked for the tail of the list.

```haskell
{-@ data SortedListHeap a =
      Nil |
      Cons {
        t :: SLH a,
        h :: {v:a | IsMin v t}
      }
  @-}

{-@ predicate IsMin N H = (hsize H == 0) || (N <= hmin H) @-}
```

## [Leftist Heap](src/Heap/LeftistHeap.hs)

The Leftist Heap is a more legitimate heap implementation that *is* included in
book. The data structure is a binary tree where the element at the root node
is at least as small as the elements at both of the children. The Leftist Heap also
requires that the rank (length of the shortest path to a leaf node) of the right
sub-heap is smaller than the rank of the left sub-heap. Both of these properties
are encoded in the refinement type for the heaps constructor.

```haskell
{-@ data LeftistHeap a =
      E |
      T
        (r     :: {v:Nat | v > 0})
        (left  :: LH a)
        (right :: {v:LH a | (rank v == r - 1) &&
                            (rank left >= rank v)})
        (val   :: {v:a | IsMin v left && IsMin v right} )
  @-}
```

The implementation of `merge` for this heap is particularly interesting.
LiquidHaskell was not able to verify the Leftist Heap merge function given in
*Purely Functional Data Structures*. I believe that this was because LiquidHaskell
could not show that minimum after merging two heaps must be the minimum of one
of the input heaps. I was able to encode a variant of this fact into the type
of `merge` in a way that enabled LiquidHaskell to check the function.

The new type of the function says that any element that is at least as small as
the minimum of both input heaps must be at least as small as the minimum of the
output heap. The way this is written is unnecessarily heavy - to encode universal
quantification, a new parameter is added to the function that is not used anywhere
inside the body of the function. I would like to further modify the type to remove
the extra parameter.

```haskell
{-@ merge_aux :: forall a. Ord a =>
      e:a ->
      h0:LH a ->
      h1:LH a ->
      {h2:LH a | (hsize h2 == hsize h0 + hsize h1) &&
                 (IsMin e h0 ==> IsMin e h1 ==> IsMin e h2)}
  @-}
```

# [Random-Access Lists](src/RandomAccessList/RandomAccessList.hs).

A random-access list as presented in *Purely Functional Data Structures* is an
extension of the usual cons-list that supports lookup and update functions like
those you would expect to see for a traditional array. While for a queue it
sufficed to know that the structure was not empty before retrieving the next
element, a random access list must verify that a requested index is with the
bounds of the list before any lookup or update operation. This requirement is
encoded in the refinement types for these functions.

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
