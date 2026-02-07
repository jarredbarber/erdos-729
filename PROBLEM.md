# Erdos Problem

## Background / Context

Erdős [Er68c] proved that if a!b!∣n! then a+b≤n+O(logn). The proof is easy, and can be done with powers of 2 alone: 
> Legendre's formula implies that if 2k is the highest power of 2 dividing n! then k=n+O(logn), and hence if a!b!∣n! then a+b≤n+O(logn).

## Problem statement

This problem is asking if a!b!∣n! 'ignoring what happens on small primes' still implies a+b≤n+O(logn).

This has been proved in the affirmative by Barreto and Leeham, using ChatGPT and Aristotle

## Goal
The goal is to produce a natural language proof as well as a Lean proof of the theorem.

Success criteria:

1. The main theorem *statement* in Lean corresponds to the natural language problem statement and does not make additional assumptions.
2. The Lean theorem compiles with `lake build`
3. There are no sorrys in the codebase. Upstream sorrys stemming from inside of mathlib are acceptable, but you may *not* introduce new ones.

ALL THREE MUST BE SATISFIED FOR SUCCESS


You may pull in mathlib; the mathlib reference is at: https://leanprover-community.github.io/mathlib4_docs/


