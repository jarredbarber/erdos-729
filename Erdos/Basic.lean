import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

set_option linter.style.longLine false
-- set_option maxHeartbeats 800000 -- applied per-declaration where needed

open Nat Real

/-!
# Erdős Factorial Divisibility Theorem (Ignoring Small Primes)
-/

def IgnoresSmallPrimes (a b n P : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p > P →
    padicValNat p a.factorial + padicValNat p b.factorial ≤
    padicValNat p n.factorial

/-! ## Proved helper lemmas -/

lemma vpn_zero_of_gt {p n : ℕ} (hp : p.Prime) (h : p > n) :
    padicValNat p n.factorial = 0 :=
  padicValNat.eq_zero_of_not_dvd (mt hp.dvd_factorial.mp (by omega))

/-- Legendre's formula gives: a + b ≤ n + s_q(a) + s_q(b) -/
lemma key_ineq (p a b n : ℕ) [hp : Fact p.Prime]
    (h : padicValNat p a.factorial + padicValNat p b.factorial ≤ padicValNat p n.factorial) :
    a + b ≤ n + (Nat.digits p a).sum + (Nat.digits p b).sum := by
  have ha := sub_one_mul_padicValNat_factorial (p := p) a
  have hb := sub_one_mul_padicValNat_factorial (p := p) b
  have hn := sub_one_mul_padicValNat_factorial (p := p) n
  have h' := Nat.mul_le_mul_left (p - 1) h
  rw [Nat.left_distrib, ha, hb, hn] at h'
  have := Nat.digit_sum_le p a
  have := Nat.digit_sum_le p b
  omega

/-- Digit sum ≤ (p-1) * (Nat.log p n + 1) -/
lemma list_sum_le_mul_length (l : List ℕ) (b : ℕ) (h : ∀ d ∈ l, d ≤ b) :
    l.sum ≤ b * l.length := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    simp only [List.sum_cons, List.length_cons]
    have hd : d ≤ b := h d (by simp)
    have hds : ds.sum ≤ b * ds.length := ih (fun x hx => h x (by simp [hx]))
    calc d + ds.sum ≤ b + b * ds.length := Nat.add_le_add hd hds
      _ = b * (ds.length + 1) := by ring

lemma digit_sum_bound (p n : ℕ) (hp : 1 < p) (hn : n ≠ 0) :
    (Nat.digits p n).sum ≤ (p - 1) * (Nat.log p n + 1) := by
  have h2 : (Nat.digits p n).sum ≤ (p - 1) * (Nat.digits p n).length := by
    apply list_sum_le_mul_length
    intro d hd
    exact Nat.le_pred_of_lt (Nat.digits_lt_base hp hd)
  rw [Nat.digits_len p n hp hn] at h2; exact h2

/-- For prime q > max(P,n), a < q. -/
lemma a_lt_large_prime (a b n P q : ℕ) (hq : q.Prime) (hqP : q > P) (hqn : q > n)
    (hign : IgnoresSmallPrimes a b n P) : a < q := by
  by_contra h; push_neg at h
  have := hign q hq hqP
  rw [vpn_zero_of_gt hq hqn] at this
  have : 0 < padicValNat q a.factorial := by
    rw [Nat.pos_iff_ne_zero]; intro h0
    rcases padicValNat.eq_zero_iff.mp h0 with h1 | h2 | h3
    · exact absurd h1 hq.one_lt.ne'
    · exact absurd h2 (Nat.factorial_pos a).ne'
    · exact absurd (hq.dvd_factorial.mpr h) h3
  omega

lemma b_lt_large_prime (a b n P q : ℕ) (hq : q.Prime) (hqP : q > P) (hqn : q > n)
    (hign : IgnoresSmallPrimes a b n P) : b < q := by
  have hign' : IgnoresSmallPrimes b a n P := fun p hp hpP => by have := hign p hp hpP; omega
  exact a_lt_large_prime b a n P q hq hqP hqn hign'

/-! ## Main theorem — NEEDS PROOF -/

theorem erdos_factorial_ignoring_small_primes (P : ℕ) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (a b n : ℕ),
      IgnoresSmallPrimes a b n P →
      ((a + b : ℕ) : ℝ) ≤ (n : ℝ) + C * Real.log ((n : ℝ) + 2) := by
  sorry
