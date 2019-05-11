---
title: "Liquid-Structures: statically verifying data structure invariants with LiquidHaskell"
author: "John Kastner"
toc: yes
---

## Introduction

  * Goal: statically verify data structure invariants
  * Data structure implementations adapted from *Purely Functional Data Structures*
  * LiquidHaskell's refinement types used to encode and statically check invariants

# LiquidHaskell

## LiquidHaskell

* An extension to the Haskell programming language
* Haskell already has a strong static type system but, it lacks dependant types
  such as those in Coq
* LiquidHaskell lets you annotate types with logical predicates (refinements)
* This is less powerful than Coq's dependant types because predicates must be
  solvable by an SMT solver

## Refinement Types

* Consider a trivial Haskell expression: `1`
* Its type: `Int`
* This doesn't precisely characterize the expression. Refinement types can be
  used to improve the specification.

```haskell
{-@ x :: {n:Int | n > 0} @-}
x :: Int
x = 1
```

```haskell
{-@ y :: {n:Int | n == 1} @-}
y :: Int
y = 1
```

## Refining Functions

Refinement types are much more interesting when applied to function argument
types and return types.

### Postconditions

```haskell
{-@ abs :: n:Int -> {m:Int | m >= 0} @-}
abs n | n < 0     = - n
      | otherwise = n
```

### Preconditions

```haskell
{-@ safeDiv :: n:Int -> d:{v:Int | v /= 0} -> Int @-}
safeDiv n d = n `div` d
```

### Interesting Combinations

```haskell
{-@ fib :: {n:Int | n >= 0} -> {v:Int | v >= 0} @-}
fib n | n <= 1    = n
      | otherwise = fib (n - 1) + fib (n - 2)
```

## Refining Data Types

# Banker's Queue

# Binary Search Tree

# Red-Black Tree
