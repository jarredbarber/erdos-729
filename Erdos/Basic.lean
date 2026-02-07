import Mathlib

/-!
# Erdős Factorial Divisibility Theorem (Ignoring Small Primes)

This file contains the formalization of the Erdős conjecture that if a!b! divides n!
"ignoring what happens on small primes", then a + b ≤ n + O(log n).

## References

* [Er68c] P. Erdős, "Some problems and results in elementary number theory"
-/

open scoped Nat

/--
The divisibility condition holds when ignoring small primes:
For all primes p > P, the p-adic valuation of a!b! does not exceed that of n!.
-/
def IgnoresSmallPrimes (a b n P : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p > P →
    padicValNat p a.factorial + padicValNat p b.factorial ≤
    padicValNat p n.factorial

/-- For primes q > n, we have v_q(n!) = 0. -/
lemma padicValNat_factorial_eq_zero_of_prime_gt {q n : ℕ} (hq : q.Prime) (hgt : q > n) :
    padicValNat q n.factorial = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro hdvd
  have := hq.dvd_factorial.mp hdvd
  omega

/-- If v_p(m!) = 0 for a prime p and m > 0, then m < p. -/
lemma lt_of_padicValNat_factorial_eq_zero {p m : ℕ} (hp : p.Prime) (hm : m > 0)
    (h : padicValNat p m.factorial = 0) : m < p := by
  by_contra hge
  push_neg at hge
  have hdvd : p ∣ m.factorial := hp.dvd_factorial.mpr hge
  haveI : Fact p.Prime := ⟨hp⟩
  have hpos : padicValNat p m.factorial ≥ 1 :=
    one_le_padicValNat_of_dvd (Nat.factorial_ne_zero m) hdvd
  omega

/-- The p-adic constraint implies a bound via digit sums. -/
lemma constraint_gives_bound_via_digits (p a b n : ℕ) (hp : p.Prime)
    (h : padicValNat p a.factorial + padicValNat p b.factorial ≤ padicValNat p n.factorial) :
    a + b ≤ n + (Nat.digits p a).sum + (Nat.digits p b).sum := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha : (p - 1) * padicValNat p a.factorial = a - (Nat.digits p a).sum :=
    sub_one_mul_padicValNat_factorial a
  have hb : (p - 1) * padicValNat p b.factorial = b - (Nat.digits p b).sum :=
    sub_one_mul_padicValNat_factorial b
  have hn' : (p - 1) * padicValNat p n.factorial = n - (Nat.digits p n).sum :=
    sub_one_mul_padicValNat_factorial n
  have hmul : (p - 1) * (padicValNat p a.factorial + padicValNat p b.factorial) ≤
              (p - 1) * padicValNat p n.factorial := Nat.mul_le_mul_left (p - 1) h
  rw [Nat.mul_add, ha, hb, hn'] at hmul
  omega

/-- Digit sum bound: s_p(m) ≤ (p-1) * (log_p(m) + 1) for m > 0. -/
lemma digit_sum_le_log_bound (p m : ℕ) (hp : 1 < p) (hm : m > 0) :
    (Nat.digits p m).sum ≤ (p - 1) * (Nat.log p m + 1) := by
  have hlen : (Nat.digits p m).length = Nat.log p m + 1 :=
    Nat.digits_len p m hp (Nat.ne_of_gt hm)
  have hdig : ∀ d ∈ Nat.digits p m, d ≤ p - 1 := fun d hd =>
    Nat.le_pred_of_lt (Nat.digits_lt_base hp hd)
  have hsum : (Nat.digits p m).sum ≤ (Nat.digits p m).length * (p - 1) := by
    induction Nat.digits p m with
    | nil => simp
    | cons d ds ih =>
      simp only [List.sum_cons, List.length_cons]
      have hd : d ≤ p - 1 := hdig d (List.mem_cons_self d ds)
      have hds : ds.sum ≤ ds.length * (p - 1) :=
        ih (fun x hx => hdig x (List.mem_cons_of_mem d hx))
      omega
  omega

/-- Nat.log b n ≤ log(n) / log(b) for n > 0, b > 1. -/
lemma nat_log_le_real_log_div (b n : ℕ) (hb : 1 < b) (hn : 0 < n) :
    (Nat.log b n : ℝ) ≤ Real.log n / Real.log b := by
  have hlog_b_pos : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  have h := Nat.pow_log_le_self b (Nat.ne_of_gt hn)
  have h' : (b : ℝ) ^ (Nat.log b n) ≤ n := by rw [← Nat.cast_pow]; exact_mod_cast h
  have hpow_pos : (0 : ℝ) < b ^ Nat.log b n := by positivity
  have hlog_mono := Real.log_le_log hpow_pos h'
  rw [Real.log_pow] at hlog_mono
  rw [le_div_iff₀ hlog_b_pos]
  linarith

/-- log(2) > 0.3 -/
lemma log_two_gt_point_three : Real.log 2 > (0.3 : ℝ) := by native_decide

/-- log(3) > 1 -/
lemma log_three_gt_one : Real.log 3 > 1 := by native_decide

/--
**Main Theorem (Erdős Factorial Divisibility with Small Primes Ignored)**

If a!b! divides n! when ignoring small primes, then a + b ≤ n + O(log n).
-/
theorem erdos_factorial_ignoring_small_primes (P : ℕ) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (a b n : ℕ),
      IgnoresSmallPrimes a b n P →
      ((a + b : ℕ) : ℝ) ≤ (n : ℝ) + C * Real.log ((n : ℝ) + 2) := by
  -- Get a prime q > P
  obtain ⟨q, hq_ge, hq_prime⟩ := Nat.exists_infinite_primes (P + 1)
  have hq_gt : q > P := Nat.lt_of_succ_le hq_ge
  have hq1 : 1 < q := hq_prime.one_lt
  haveI : Fact q.Prime := ⟨hq_prime⟩
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq1
  have hq_pos : (0 : ℝ) < q := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_gt : Real.log 2 > 0.3 := log_two_gt_point_three
  have hlog3_gt : Real.log 3 > 1 := log_three_gt_one
  -- Choose C = 500 * q^2
  use 500 * (q : ℝ)^2
  constructor
  · positivity
  intro a b n h_ign
  have h_constraint := h_ign q hq_prime hq_gt
  have hlog_n2_pos : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith : (1 : ℝ) < n + 2)
  have hlog_n2_ge : Real.log ((n : ℝ) + 2) ≥ Real.log 2 := by
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 2); linarith
  -- Use Bertrand to bound a and b
  by_cases hmaxz : max P n = 0
  · -- max(P, n) = 0 means P = 0 and n = 0
    have hPn : P = 0 ∧ n = 0 := Nat.max_eq_zero_iff.mp hmaxz
    obtain ⟨hP, hn⟩ := hPn
    subst hP hn
    simp only [Nat.factorial_zero, Nat.cast_zero, zero_add] at h_constraint ⊢
    have hvq0 : padicValNat q 1 = 0 := by simp [padicValNat]
    rw [hvq0] at h_constraint
    have hva0 : padicValNat q a.factorial = 0 := Nat.eq_zero_of_add_eq_zero_right
      (Nat.le_antisymm h_constraint (Nat.zero_le _))
    have hvb0 : padicValNat q b.factorial = 0 := Nat.eq_zero_of_add_eq_zero_left
      (Nat.le_antisymm h_constraint (Nat.zero_le _))
    have ha_lt : a < q := by
      by_cases ha0 : a = 0; · omega
      exact lt_of_padicValNat_factorial_eq_zero hq_prime (Nat.pos_of_ne_zero ha0) hva0
    have hb_lt : b < q := by
      by_cases hb0 : b = 0; · omega
      exact lt_of_padicValNat_factorial_eq_zero hq_prime (Nat.pos_of_ne_zero hb0) hvb0
    have hab : (a + b : ℝ) < 2 * q := by
      have h : a + b < 2 * q := by omega
      exact_mod_cast h
    -- 2*q ≤ q^2 ≤ 500*q^2*log(2)
    have h1 : (2 : ℝ) * q ≤ q * q := by nlinarith
    have h2 : (q : ℝ) * q ≤ 500 * q^2 * Real.log 2 := by
      have h3 : 500 * (q : ℝ)^2 * Real.log 2 ≥ 500 * q^2 * 0.3 := by nlinarith [sq_nonneg (q : ℝ)]
      have h4 : 500 * (q : ℝ)^2 * 0.3 = 150 * q^2 := by ring
      have h5 : (q : ℝ)^2 ≤ 150 * q^2 := by nlinarith [sq_nonneg (q : ℝ)]
      have h6 : q * q = q^2 := by ring
      linarith
    linarith [hlog_n2_ge]
  · -- max(P, n) > 0
    have hmax_pos : max P n > 0 := Nat.pos_of_ne_zero hmaxz
    obtain ⟨p', hp'_prime, hp'_gt, hp'_le⟩ := Nat.bertrand (max P n) (Nat.ne_of_gt hmax_pos)
    have hp'_gt_P : p' > P := Nat.lt_of_le_of_lt (le_max_left P n) hp'_gt
    have hp'_gt_n : p' > n := Nat.lt_of_le_of_lt (le_max_right P n) hp'_gt
    have h_constraint' := h_ign p' hp'_prime hp'_gt_P
    have hvn0 : padicValNat p' n.factorial = 0 := padicValNat_factorial_eq_zero_of_prime_gt hp'_prime hp'_gt_n
    rw [hvn0] at h_constraint'
    have hva0 : padicValNat p' a.factorial = 0 := Nat.eq_zero_of_add_eq_zero_right
      (Nat.le_antisymm h_constraint' (Nat.zero_le _))
    have hvb0 : padicValNat p' b.factorial = 0 := Nat.eq_zero_of_add_eq_zero_left
      (Nat.le_antisymm h_constraint' (Nat.zero_le _))
    have ha_lt : a < p' := by
      by_cases ha0 : a = 0; · omega
      exact lt_of_padicValNat_factorial_eq_zero hp'_prime (Nat.pos_of_ne_zero ha0) hva0
    have hb_lt : b < p' := by
      by_cases hb0 : b = 0; · omega
      exact lt_of_padicValNat_factorial_eq_zero hp'_prime (Nat.pos_of_ne_zero hb0) hvb0
    -- a, b < p' ≤ 2 * max(P, n)
    have hab_bound : a + b < 2 * p' := by omega
    have hab_le : a + b ≤ 4 * max P n := by omega
    -- Use the digit constraint from prime q
    have h_via_digits := constraint_gives_bound_via_digits q a b n hq_prime h_constraint
    -- Bound digit sums
    have hsa := Nat.digit_sum_le q a
    have hsb := Nat.digit_sum_le q b
    have hmax_le : max P n ≤ n + P := by simp [max_def]; split_ifs <;> omega
    -- Split cases based on a, b being 0 or positive
    have hab_via_digits : (a + b : ℝ) ≤ n + (Nat.digits q a).sum + (Nat.digits q b).sum := by
      exact_mod_cast h_via_digits
    -- Key insight: digit sum s_q(m) ≤ m, and we have a + b ≤ n + s_q(a) + s_q(b)
    -- For a better bound, we need s_q(m) = O(log m).
    -- s_q(m) ≤ (q-1)*(log_q(m)+1) and log_q(m) ≤ log(m)/log(q) ≤ log(m)/log(2)
    -- For m < 2*max(P,n) ≤ 2*(n+P): log(m) ≤ log(2*(n+P)) = log(2) + log(n+P)
    -- Since n+P ≤ (n+2)*(P+1) for n,P ≥ 0: log(n+P) ≤ log(n+2) + log(P+1)
    -- And log(P+1) ≤ P (for P ≥ 1) or log(P+1) = log(1) = 0 (for P = 0)
    -- So s_q(m) ≤ (q-1) * (C' * log(n+2) + D) for some constants C', D depending on P and q.
    -- For simplicity, we bound more coarsely:
    -- a + b ≤ n + s_q(a) + s_q(b) ≤ n + a + b (from digit_sum_le)
    -- This trivially holds but doesn't give O(log n).
    -- Better: s_q(a) + s_q(b) ≤ 2*(q-1)*(max(log_q(a), log_q(b))+1)
    -- For a, b < 2*max(P,n): max(log_q(a), log_q(b)) ≤ log_q(2*max(P,n))
    --                      ≤ log(2*max(P,n))/log(q) ≤ log(2*(n+P))/log(2)
    -- log(2*(n+P)) ≤ log(2) + log(n+P+1) ≤ 1 + log(n+P+1) ≤ 1 + log((n+2)*(P+1))
    --             = 1 + log(n+2) + log(P+1) ≤ 1 + log(n+2) + P (using log(P+1) ≤ P)
    -- So s_q(a) + s_q(b) ≤ 2*q*(log(n+2) + P + 2)/log(2) ≤ 2*q*(log(n+2) + P + 2)*4
    --                   = 8*q*log(n+2) + 8*q*(P+2)
    -- For log(n+2) ≥ 1 (n ≥ 1): 8*q*(P+2) ≤ 8*q*(P+2)*log(n+2)
    -- So s_q(a) + s_q(b) ≤ (8*q + 8*q*(P+2))*log(n+2) = 8*q*(P+3)*log(n+2)
    -- Since q > P: P < q, so P+3 < q+3 ≤ 2*q (for q ≥ 3)
    -- For q = 2: P < 2, P ∈ {0, 1}, P+3 ∈ {3, 4} ≤ 2*2 = 4. OK.
    -- So s_q(a) + s_q(b) ≤ 8*q*2*q*log(n+2) = 16*q^2*log(n+2) ≤ 500*q^2*log(n+2)
    -- a + b ≤ n + 16*q^2*log(n+2) ≤ n + 500*q^2*log(n+2) ✓
    -- For n = 0: We need to handle separately.
    by_cases hn0 : n = 0
    · -- n = 0, max(P, 0) = P > 0
      subst hn0
      simp only [max_eq_left (Nat.zero_le P), Nat.cast_zero, zero_add] at *
      -- a + b ≤ 4*P and we need a + b ≤ 500*q^2*log(2)
      have hab_4P : (a + b : ℝ) ≤ 4 * P := by exact_mod_cast hab_le
      have hP1_le_q : (P : ℝ) + 1 ≤ q := by exact_mod_cast hq_ge
      -- 4*P ≤ 4*(q-1) ≤ 4*q ≤ 4*q^2 (for q ≥ 1)
      -- 500*q^2*log(2) ≥ 500*q^2*0.3 = 150*q^2 ≥ 4*q^2 ≥ 4*q ≥ 4*P
      have h1 : (4 : ℝ) * P ≤ 4 * (q - 1) := by linarith
      have h2 : (4 : ℝ) * (q - 1) ≤ 4 * q := by linarith
      have h3 : (4 : ℝ) * q ≤ 4 * q^2 := by nlinarith [sq_nonneg (q : ℝ)]
      have h4 : (4 : ℝ) * q^2 ≤ 150 * q^2 := by nlinarith [sq_nonneg (q : ℝ)]
      have h5 : (150 : ℝ) * q^2 ≤ 500 * q^2 * Real.log 2 := by
        have h6 : 500 * (q : ℝ)^2 * Real.log 2 ≥ 500 * q^2 * 0.3 := by nlinarith [sq_nonneg (q : ℝ)]
        linarith
      linarith [hlog_n2_ge]
    · -- n ≥ 1
      have hn_pos : n ≥ 1 := Nat.pos_of_ne_zero hn0
      have hn2_ge_3 : (n : ℝ) + 2 ≥ 3 := by
        have h : (1 : ℝ) ≤ n := by exact_mod_cast hn_pos
        linarith
      have hlog_n2_ge_1 : Real.log ((n : ℝ) + 2) ≥ 1 := by
        have hlog3_ge_1 : Real.log (3 : ℝ) > 1 := hlog3_gt
        have hlog_mono : Real.log (3 : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
          Real.log_le_log (by norm_num : (0 : ℝ) < 3) hn2_ge_3
        linarith
      -- Now use the digit sum bound.
      -- s_q(a) ≤ a and s_q(b) ≤ b, so s_q(a) + s_q(b) ≤ a + b ≤ 4*max(P,n)
      -- We need to bound s_q(a) + s_q(b) in terms of log(n+2).
      -- Key: s_q(m) ≤ (q-1)*(log_q(m)+1) for m > 0.
      -- For m = 0: s_q(0) = 0.
      -- For 0 < m < 2*max(P,n): log_q(m) ≤ log(m)/log(q) ≤ log(2*max(P,n))/log(2)
      -- log(2*max(P,n)) ≤ log(2) + log(n+P) (since max(P,n) ≤ n+P)
      -- log(n+P) ≤ log((n+2)*(P+1)) = log(n+2) + log(P+1) (for n+P ≤ (n+2)*(P+1), which holds)
      -- log(P+1) ≤ P+1 (since log(x) ≤ x-1 for x ≥ 1, so log(x) ≤ x for x ≥ 1)
      -- So log_q(m) ≤ (log(2) + log(n+2) + P+1)/log(2) ≤ (1 + log(n+2) + P+1)/0.3
      --            ≤ 4*(P + 2 + log(n+2))
      -- s_q(m) ≤ (q-1)*(4*(P+2+log(n+2))+1) ≤ q*5*(P+3+log(n+2))
      --       = 5*q*(P+3) + 5*q*log(n+2)
      -- For log(n+2) ≥ 1: 5*q*(P+3) ≤ 5*q*(P+3)*log(n+2)
      -- s_q(m) ≤ 5*q*(P+4)*log(n+2)
      -- Since q > P: P+4 < q+4 ≤ 2*q (for q ≥ 4)
      -- For q = 2, 3: P < q, so P ≤ q-1. P+4 ≤ q+3.
      --   For q = 2: P ≤ 1, P+4 ≤ 5, 2*2 = 4 < 5. So P+4 ≤ 3*q = 6.
      --   For q = 3: P ≤ 2, P+4 ≤ 6, 2*3 = 6. So P+4 ≤ 2*q.
      -- So s_q(m) ≤ 5*q*3*q*log(n+2) = 15*q^2*log(n+2) for q ≥ 2.
      -- s_q(a) + s_q(b) ≤ 30*q^2*log(n+2) ≤ 500*q^2*log(n+2) ✓
      -- a + b ≤ n + 30*q^2*log(n+2) ≤ n + 500*q^2*log(n+2) ✓
      -- Now let's formalize a simpler bound:
      -- From hab_le: a + b ≤ 4*max(P, n) ≤ 4*(n + P)
      -- From h_via_digits: a + b ≤ n + s_q(a) + s_q(b)
      -- And s_q(a) + s_q(b) ≤ a + b ≤ 4*(n + P) = 4*n + 4*P
      -- So a + b ≤ n + 4*n + 4*P = 5*n + 4*P
      -- This is O(n), not O(log n)! We need the finer bound on digit sums.
      -- Let's use the log bound directly.
      -- Case on a = 0 or a > 0, and b = 0 or b > 0.
      -- If both a = 0 and b = 0: a + b = 0 ≤ n ≤ n + C*log(n+2). ✓
      -- If a = 0, b > 0: a + b = b ≤ n + s_q(b). And s_q(b) ≤ (q-1)*(log_q(b)+1).
      --   From b < 2*max(P,n) ≤ 2*(n+P): log(b) < log(2*(n+P))
      --   ... (complex)
      -- For simplicity, let me use a direct approach:
      -- The key observation is that a + b ≤ n + s_q(a) + s_q(b).
      -- And for any m: s_q(m) ≤ m. So a + b ≤ n + a + b, which is trivially true.
      -- But we also know a + b ≤ 4*max(P, n).
      -- For n ≥ max(P, n)/3 (i.e., n ≥ P/2): a + b ≤ 4*max(P, n) ≤ 4*(2n) = 8n
      --   Then a + b ≤ 8n ≤ n + 7n. We need 7n ≤ 500*q^2*log(n+2).
      --   For n ≤ 500*q^2: log(n+2) ≥ log(2) > 0.3, so 500*q^2*log(n+2) > 150*q^2 ≥ 150*4 = 600 > 7*n?
      --     Only if n < 600/7 ≈ 85. So this doesn't work for large n.
      -- The correct approach requires the digit sum to be O(log m), not O(m).
      -- Let me try a more direct computation.
      -- From h_via_digits: a + b ≤ n + s_q(a) + s_q(b)
      -- For a > 0: s_q(a) ≤ (q-1)*(log_q(a)+1)
      -- log_q(a) = log(a)/log(q). For a < 2*max(P,n) ≤ 2*(n+P):
      -- log(a) < log(2*(n+P)) = log(2) + log(n+P)
      -- log(n+P) < log((n+2)*(P+1)) = log(n+2) + log(P+1) (for n+P < (n+2)*(P+1) ⟺ nP + P + 2 > 0, true)
      -- log(P+1) ≤ P + 1 (since log(x) ≤ x for x ≥ 1 follows from e^x ≥ x for x ≥ 0)
      -- So log(a) < log(2) + log(n+2) + P + 1 < 1 + log(n+2) + P + 1 = log(n+2) + P + 2
      -- log_q(a) < (log(n+2) + P + 2)/log(q) ≤ (log(n+2) + P + 2)/log(2)
      --         < (log(n+2) + P + 2)/0.3 (using log(2) > 0.3)
      --         ≤ 4*(log(n+2) + P + 2) (since 1/0.3 < 4)
      -- s_q(a) ≤ (q-1)*(4*(log(n+2) + P + 2) + 1) ≤ q*(4*log(n+2) + 4*P + 9)
      -- Similarly for s_q(b) if b > 0.
      -- If a = 0: s_q(a) = 0.
      -- So s_q(a) + s_q(b) ≤ 2*q*(4*log(n+2) + 4*P + 9) = 8*q*log(n+2) + q*(8*P + 18)
      -- For log(n+2) ≥ 1: q*(8*P + 18) ≤ q*(8*P + 18)*log(n+2)
      -- s_q(a) + s_q(b) ≤ (8*q + q*(8*P + 18))*log(n+2) = q*(8*P + 26)*log(n+2)
      -- Since q > P: 8*P + 26 < 8*q + 26 ≤ 34*q (for q ≥ 1)
      -- Actually, 8*P + 26 ≤ 8*(q-1) + 26 = 8*q + 18 (since P ≤ q-1)
      -- So s_q(a) + s_q(b) ≤ q*(8*q + 18)*log(n+2) ≤ (8*q^2 + 18*q)*log(n+2)
      --                   ≤ 26*q^2*log(n+2) (for q ≥ 18/18 = 1)
      -- a + b ≤ n + 26*q^2*log(n+2) ≤ n + 500*q^2*log(n+2) ✓
      -- The formalization below follows this outline but with careful handling of edge cases.
      -- Key bounds we need:
      have hP_lt_q : (P : ℝ) < q := by exact_mod_cast hq_gt
      have hP_le_q1 : (P : ℝ) ≤ q - 1 := by linarith
      have h8P26 : (8 : ℝ) * P + 26 ≤ 8 * q + 18 := by linarith
      have hq_sq_bound : (8 : ℝ) * q + 18 ≤ 26 * q := by nlinarith
      have hcoeff : (8 : ℝ) * P + 26 ≤ 26 * q := by linarith
      -- Bound digit sums
      have hsa_bound : ((Nat.digits q a).sum : ℝ) ≤ q * (4 * Real.log ((n : ℝ) + 2) + 4 * P + 9) := by
        by_cases ha0 : a = 0
        · subst ha0
          simp only [Nat.digits_zero, List.sum_nil, Nat.cast_zero]
          have h := sq_nonneg (q : ℝ)
          nlinarith [hlog_n2_pos]
        · have ha_pos : a > 0 := Nat.pos_of_ne_zero ha0
          have hsa_log := digit_sum_le_log_bound q a hq1 ha_pos
          have hsa_real : ((Nat.digits q a).sum : ℝ) ≤ (q - 1) * ((Nat.log q a : ℝ) + 1) := by
            exact_mod_cast hsa_log
          -- Bound Nat.log q a
          have ha_lt_2max : a < 2 * max P n := by omega
          have ha_lt_2np : (a : ℝ) < 2 * ((n : ℝ) + P) := by
            have h1 : a < 2 * max P n := ha_lt_2max
            have h2 : max P n ≤ n + P := hmax_le
            have h3 : (a : ℝ) < 2 * (max P n : ℝ) := by exact_mod_cast h1
            have h4 : (max P n : ℝ) ≤ (n : ℝ) + P := by exact_mod_cast h2
            linarith
          have hlog_a_bound : Real.log a < Real.log ((n : ℝ) + 2) + (P : ℝ) + 2 := by
            have h1 : Real.log a < Real.log (2 * ((n : ℝ) + P)) := by
              apply Real.log_lt_log (by exact_mod_cast ha_pos : (0 : ℝ) < a) ha_lt_2np
            have h2 : Real.log (2 * ((n : ℝ) + P)) = Real.log 2 + Real.log ((n : ℝ) + P) := by
              rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)]
              · ring
              · have hnP_pos : (n : ℝ) + P > 0 := by
                  have h := Nat.cast_pos.mpr hn_pos
                  linarith
                linarith
            have h3 : Real.log ((n : ℝ) + P) ≤ Real.log ((n : ℝ) + 2) + Real.log ((P : ℝ) + 1) := by
              have hnP_bound : (n : ℝ) + P ≤ (n + 2) * (P + 1) := by nlinarith
              have hnP_pos : (0 : ℝ) < n + P := by
                have h := Nat.cast_pos.mpr hn_pos
                linarith
              calc Real.log ((n : ℝ) + P)
                  ≤ Real.log ((n + 2) * (P + 1)) := Real.log_le_log hnP_pos hnP_bound
                _ = Real.log ((n : ℝ) + 2) + Real.log ((P : ℝ) + 1) := by
                    rw [Real.log_mul (by linarith : (n : ℝ) + 2 ≠ 0) (by linarith : (P : ℝ) + 1 ≠ 0)]
            have h4 : Real.log ((P : ℝ) + 1) ≤ P + 1 := by
              have h5 : Real.log ((P : ℝ) + 1) ≤ (P + 1) - 1 := by
                apply Real.log_le_sub_one_of_le
                linarith
              linarith
            have h5 : Real.log 2 < 1 := by
              have h := Real.log_le_sub_one_of_le (by norm_num : (2 : ℝ) ≥ 1)
              linarith
            linarith
          have hlog_q_pos : Real.log q > 0 := Real.log_pos (by exact_mod_cast hq1 : (1 : ℝ) < q)
          have hlog_q_ge : Real.log q ≥ Real.log 2 := Real.log_le_log (by norm_num) hq2
          have hnat_log_a : (Nat.log q a : ℝ) ≤ Real.log a / Real.log q :=
            nat_log_le_real_log_div q a hq1 ha_pos
          have hnat_log_a_bound : (Nat.log q a : ℝ) < 4 * (Real.log ((n : ℝ) + 2) + P + 2) := by
            have h1 : Real.log a / Real.log q < Real.log a / Real.log 2 := by
              apply div_lt_div_of_pos_left
              · exact Real.log_pos (by exact_mod_cast ha_pos : (1 : ℝ) < a + 1)
                -- Actually need log(a) > 0 iff a > 1. For a = 1: log(1) = 0, so div is 0.
                -- Let me just use the bound more carefully.
              sorry -- Type issue, let me simplify
            sorry
          sorry
      sorry
