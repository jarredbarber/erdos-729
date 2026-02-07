import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Erdős Factorial Divisibility Theorem (Ignoring Small Primes)

This file contains the formalization of the Erdős conjecture that if a!b! divides n!
"ignoring what happens on small primes", then a + b ≤ n + O(log n).

## Main Results

- `erdos_factorial_ignoring_small_primes`: The main theorem stating that divisibility
  when restricted to large primes still implies the logarithmic bound on a + b.

## References

* [Er68c] P. Erdős, "Some problems and results in elementary number theory"
-/

/--
The divisibility condition holds when ignoring small primes:
For all primes p > P, the p-adic valuation of a!b! does not exceed that of n!.
This is equivalent to saying v_p(a!) + v_p(b!) ≤ v_p(n!) for all primes p > P.
-/
def IgnoresSmallPrimes (a b n P : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p > P → 
    padicValNat p (Nat.factorial a) + padicValNat p (Nat.factorial b) ≤ 
    padicValNat p (Nat.factorial n)

/--
**Main Theorem (Erdős Factorial Divisibility with Small Primes Ignored)**

If a!b! divides n! when ignoring small primes (i.e., the divisibility condition holds
for all sufficiently large primes), then a + b ≤ n + O(log n).

More precisely: There exist constants C > 0 and P₀ such that for all a, b, n, P
satisfying P ≥ P₀ and the divisibility condition for primes > P, we have
a + b ≤ n + C * log(n + 1).

Note: We use log(n + 1) instead of log(n) to avoid issues when n = 0.
-/
theorem erdos_factorial_ignoring_small_primes :
    ∃ (C : ℝ) (P₀ : ℕ), C > 0 ∧ ∀ (a b n P : ℕ), 
      P ≥ P₀ → 
      IgnoresSmallPrimes a b n P → 
      ((a + b : ℕ) : ℝ) ≤ (n : ℝ) + C * Real.log ((n : ℝ) + 1) := by
  sorry
