import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic
import Mathlib.Algebra.Order.Field.Basic

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
Legendre's formula upper bound: v_p(n!) < n / (p - 1).
-/
lemma legendre_upper_bound (p n : ℕ) [hp : Fact p.Prime] (hn : n > 0) :
    (padicValNat p (n.factorial) : ℝ) < (n : ℝ) / (p - 1) := by
  have hp1 : 1 < p := hp.out.one_lt
  have hp_sub_one_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp1
  have h_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (Nat.Prime.one_le hp.out)]
    exact Nat.cast_pos.mpr hp_sub_one_pos
  rw [lt_div_iff₀ h_pos]
  have h_sub : (p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Nat.Prime.one_le hp.out), Nat.cast_one]
  rw [h_sub, ← Nat.cast_mul]
  norm_cast
  rw [Nat.mul_comm]
  exact sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (Nat.ne_of_gt hn)

/--
Legendre's formula lower bound: (n - p * (log_p(n) + 1)) / (p - 1) ≤ v_p(n!).
This is a standard bound used to show v_p(n!) = n/(p-1) + O(log n).
-/
lemma legendre_lower_bound (p n : ℕ) [hp : Fact p.Prime] (hn : n > 0) :
    ((n : ℝ) - p * (Nat.log p n + 1)) / (p - 1) ≤ (padicValNat p (n.factorial) : ℝ) := by
  have hp1 : 1 < p := hp.out.one_lt
  have hp_sub_one_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp1
  have h_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (Nat.Prime.one_le hp.out)]
    exact Nat.cast_pos.mpr hp_sub_one_pos
  rw [div_le_iff₀ h_pos]
  have h_sub : (p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Nat.Prime.one_le hp.out), Nat.cast_one]
  rw [h_sub, ← Nat.cast_mul]
  rw [Nat.mul_comm, sub_one_mul_padicValNat_factorial n]
  have h_sum_le_n : (Nat.digits p n).sum ≤ n := Nat.digit_sum_le p n
  rw [Nat.cast_sub h_sum_le_n]
  suffices ((Nat.digits p n).sum : ℝ) ≤ p * (Nat.log p n + 1) by
    linarith
  norm_cast
  have h_sum_le_len : ∀ L : List ℕ, (∀ d ∈ L, d ≤ p - 1) → L.sum ≤ L.length * (p - 1) := by
    intro L h_all
    induction L with
    | nil => simp
    | cons d ds ih =>
      simp only [List.sum_cons, List.length_cons, Nat.add_mul, one_mul]
      rw [Nat.add_comm]
      apply Nat.add_le_add
      · apply ih
        intro x hx
        apply h_all
        apply List.mem_cons_of_mem _ hx
      · apply h_all
        apply List.mem_cons_self
  have h_sum_le_len' := h_sum_le_len (Nat.digits p n) (fun d hd => 
    Nat.le_pred_of_lt (Nat.digits_lt_base hp1 hd))
  rw [Nat.digits_len p n hp1 (Nat.ne_of_gt hn)] at h_sum_le_len'
  apply h_sum_le_len'.trans
  rw [Nat.mul_comm p]
  apply Nat.mul_le_mul_left
  exact Nat.sub_le p 1

/--
**Main Theorem (Erdős Factorial Divisibility with Small Primes Ignored)**

If a!b! divides n! when ignoring small primes (i.e., the divisibility condition holds
for all primes larger than P), then a + b ≤ n + O(log n).

More precisely: For every natural number P, there exists a constant C > 0 
such that for all a, b, n satisfying the divisibility condition for all primes p > P, 
we have a + b ≤ n + C * log(n + 2).

Note: We use log(n + 2) to ensure the logarithm is always positive and 
to provide a sufficient bound for small n.
-/
theorem erdos_factorial_ignoring_small_primes (P : ℕ) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (a b n : ℕ), 
      IgnoresSmallPrimes a b n P → 
      ((a + b : ℕ) : ℝ) ≤ (n : ℝ) + C * Real.log ((n : ℝ) + 2) := by
  sorry
