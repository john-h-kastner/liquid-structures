---
title: "Liquid-Structures: statically verifying data structure invariants with LiquidHaskell"
author: "John Kastner"
toc: yes
---

== Introduction

* Goal: statically verify data structure invariants
* Data structure implementations adapted from *Purely Functional Data Structures*
* LiquidHaskell's refinement types used to encode and statically check invariants

= LiquidHaskell

== LiquidHaskell

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

Just like functions, data types can be refined. This is done by refining the
constructor which is a function.

<!-- Regular declaration of data type. Ommited for brevity.
\begin{code}
data List a =
    Nil
  | Cons {
      hd :: a,
      tl :: List a
    }
\end{code}
-->

<!--
\begin{code}
{-@
\end{code}
-->
\begin{code}
data List a = 
    Nil
  | Cons {
      hd :: a,
      tl :: List {v : a | v >= hd}
    }
\end{code}
<!--
\begin{code}
@-}
\end{code}
-->

= Banker's Queue

= Binary Search Tree

= Red-Black Tree
