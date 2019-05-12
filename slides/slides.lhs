---
title: "Liquid-Structures: statically verifying data structure invariants with LiquidHaskell"
author: "John Kastner"
---

<!-- Preamble that will not be rendered in final output
\begin{code}
import Prelude hiding (head, tail)
\end{code}
-->

== Introduction

* Goal: statically verify data structure invariants
* Data structure implementations adapted from *Purely Functional Data Structures*
* LiquidHaskell's refinement types used to encode and statically check invariants

= LiquidHaskell

== LiquidHaskell

![](liquid_logo.png)

* An extension to the Haskell programming language
* Haskell already has a strong static type system but, it lacks dependant types
  such as those in Coq
* LiquidHaskell lets you annotate types with logical predicates (refinements)
* This is less powerful than Coq's dependant types because predicates must be
  solvable by an SMT solver

== Refinement Types

* Consider a trivial Haskell expression: `1`
* Its type: `Int`
* This doesn't precisely characterize the expression. Refinement types can be
  used to improve the specification.

\begin{code}
{-@ x :: {n:Int | n > 0} @-}
x :: Int
x = 1

{-@ y :: {n:Int | n == 1} @-}
y :: Int
y = 1
\end{code}

== Refining Functions

Refinement types are much more interesting when applied to function argument
types and return types.

=== Postconditions

<!-- Types for functions on this slide. These won't show in the final document.
\begin{code}
abs :: Int -> Int
safeDiv :: Int -> Int -> Int
fib :: Int -> Int
\end{code}
-->

\begin{code}
{-@ abs :: n:Int -> {m:Int | m >= 0} @-}
abs n | n < 0     = - n
      | otherwise = n
\end{code}

=== Preconditions

\begin{code}
{-@ safeDiv :: n:Int -> d:{v:Int | v /= 0} -> Int @-}
safeDiv n d = n `div` d
\end{code}

=== Interesting Combinations

\begin{code}
{-@ fib :: {n:Int | n >= 0} -> {v:Int | v >= 0} @-}
fib n | n <= 1    = n
      | otherwise = fib (n - 1) + fib (n - 2)
\end{code}

== Refining Data Types

* Just like functions, data types can be refined.
* This defines the usual cons list but, the tail is recursively defined as a
  list where each element must be less than or equal the head.

<!-- Regular declaration of data type. Omitted for brevity.
\begin{code}
data List a =
    Nil
  | Cons {
      hd :: a,
      tl :: List a
    }
\end{code}
-->

\begin{code}
{-@ data List a = Nil
                | Cons {
                  hd :: a,
                  tl :: List {v : a | v >= hd}
                }
  @-}
{-@ measure llen :: List a -> Nat
    llen Nil         = 0
    llen (Cons _ tl) = 1 + llen tl
  @-}
list_good = Cons 1 (Cons 2 Nil)
{- list_bad = Cons 2 (Cons 1 Nil) -}
\end{code}

= Banker's Queue

== Banker's Queue

* A Queue data structure designed for functional programming languages
* Provides efficient read access to head and append access to tail
* Maintains two lists: the first is some prefix of the queue while the second
  is the remaining suffix of the queue
* The invariant is that the prefix list cannot be shorter than the suffix list

== Banker's Queue Datatype

* The interesting refinement type is on `lenr` which states that the length of the
  rear must be less than or equal to the length of the front
* The other refinements ensure the stored lengths are in fact the real lengths.

<!--
\begin{code}
data BankersQueue a = BQ {
  lenf :: Int,
  f    :: [a],
  lenr :: Int,
  r    :: [a]
}
\end{code}
-->

\begin{code}
{-@ data BankersQueue a = BQ {
      lenf :: Nat,
      f    :: {v:[a] | len v == lenf},
      lenr :: {v:Nat | v <= lenf},
      r    :: {v:[a] | len v == lenr}
    }
  @-}
{-@ measure qlen :: BQ a -> Nat
    qlen (BQ f _ r _) = f + r
  @-}
type BQ a = BankersQueue a
\end{code}

== Smart Constructor

* How can a queue be constructed if the invariant is not known?
* Write a function to massage data with weaker constraints until the invariant
  holds.

<!--
\begin{code}
check :: Int -> [a] -> Int -> [a] -> BQ a
\end{code}
-->

\begin{code}
{-@ check ::
    vlenf : Nat              ->
    {v:[_] | len v == vlenf} ->
    vlenr : Nat              ->                    
    {v:[_] | len v == vlenr} ->
    {q:BQ _ | qlen q == (vlenf + vlenr)}
  @-}
check lenf f lenr r =
  if lenr <= lenf then
    BQ lenf f lenr r
  else
    BQ (lenf + lenr) (f ++ (reverse r)) 0 []
\end{code}

== Banker's Queue Functions
<!--
\begin{code}
snoc    :: BQ a -> a -> BQ a
head    :: BQ a -> a
tail    :: BQ a -> BQ a
\end{code}
-->

* An element can be added to a queue
* This maintains invariants and increments the length

\begin{code}
{-@ snoc ::
      q0:BQ a ->
      a ->
      {q1:BQ a | (qlen q1) == (qlen q0) + 1}
  @-}
snoc (BQ lenf f lenr r) x =
  check lenf f (lenr + 1) (x : r)
\end{code}

---

* After adding an element, it can be retreived and removed
* Both functions require non-empty queues as specified by `qlen q /= 0`

\begin{code}
{-@ head ::
      {q:BQ a | qlen q /= 0} ->
      a
  @-}
head (BQ lenf (x : f') lenr r) = x

{-@ tail ::
      {q0:BQ a | qlen q0 /= 0} ->
      {q1:BQ a | (qlen q1) == (qlen q0) - 1}
  @-}
tail (BQ lenf (x : f') lenr r) = check (lenf - 1) f' lenr r
\end{code}

= Red-Black Tree

== Red-Black Tree

* A Red-Black Tree is a binary search tree with two key invariants.
  * **Red Invariant**:  No red node has a red child.  
  * **Black Invariant**:  Every path from  the root to an empty node contains
                          the same number of black nodes
* The invariants keep the try approximately balanced
* When invariants are violated, the tree is rotated in such a way that they are
  restored

== Red-Black Tree Datatype

<!--
\begin{code}
data RedBlackSet a =
  Empty |
  Tree {
    color   :: Color,
    rbval   :: a,
    rbleft  :: RedBlackSet a,
    rbright :: RedBlackSet a
  }

{-@ measure getColor @-}
{-@ getColor :: RB a -> Color @-}
getColor Empty          = Black
getColor (Tree c _ _ _) = c

{-@ measure numBlack @-}
{-@ numBlack :: RB a -> Nat @-}
numBlack :: RB a -> Int
numBlack Empty          = 0
numBlack (Tree c _ l r) = (if c == Black then 1 else 0) + (numBlack l)

type RB a = RedBlackSet a
\end{code}
-->

\begin{code}
data Color = Red | Black deriving Eq
{-@ data RedBlackSet a = Empty |
      Tree {
        color :: Color,
        val   :: a,
        left  :: {v:RB {vv:a | vv < val} |
                   RedInvariant color v},
        right :: {v:RB {vv:a | vv > val} |
                   RedInvariant color v &&
                   BlackInvariant v left}
      }
   @-}

{-@ predicate RedInvariant C S =
      (C == Red) ==> (getColor S /= Red) @-}
{-@ predicate BlackInvariant S0 S1 =
      (numBlack S0) == (numBlack S1) @-}
\end{code}
