import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

set_option linter.style.longLine false

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

/-- Nat.log q m ≤ Real.log m / Real.log q for m > 0, q > 1 -/
lemma nat_log_le_real_log_div (q m : ℕ) (hq : 1 < q) (hm : 0 < m) :
    (Nat.log q m : ℝ) ≤ Real.log m / Real.log q := by
  have hq_pos : (0 : ℝ) < q := by positivity
  have hq_gt1 : (1 : ℝ) < q := Nat.one_lt_cast.mpr hq
  have hlogq_pos : 0 < Real.log q := Real.log_pos hq_gt1
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hpow : (q : ℕ) ^ Nat.log q m ≤ m := Nat.pow_log_le_self q (Nat.ne_of_gt hm)
  have hpow_real : (q : ℝ) ^ Nat.log q m ≤ m := by
    rw [← Nat.cast_pow]; exact Nat.cast_le.mpr hpow
  have hlog_ineq : (Nat.log q m : ℝ) * Real.log q ≤ Real.log m := by
    have h1 : Real.log ((q : ℝ) ^ Nat.log q m) ≤ Real.log m :=
      Real.log_le_log (pow_pos hq_pos _) hpow_real
    rwa [Real.log_pow] at h1
  rwa [le_div_iff₀ hlogq_pos]

/-! ## Main theorem -/

set_option maxHeartbeats 800000 in
theorem erdos_factorial_ignoring_small_primes (P : ℕ) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (a b n : ℕ),
      IgnoresSmallPrimes a b n P →
      ((a + b : ℕ) : ℝ) ≤ (n : ℝ) + C * Real.log ((n : ℝ) + 2) := by
  -- Pick a prime q > P
  obtain ⟨q, hq_ge, hq_prime⟩ := Nat.exists_infinite_primes (P + 1)
  have hq_gt : q > P := Nat.lt_of_succ_le hq_ge
  have hq1 : 1 < q := hq_prime.one_lt
  have hq2 : q ≥ 2 := hq_prime.two_le
  haveI hqFact : Fact q.Prime := ⟨hq_prime⟩

  -- Choose C = 20 * q^2 (large enough for all cases)
  use 20 * (q : ℝ)^2
  have hC_pos : (20 : ℝ) * q^2 > 0 := by positivity
  refine ⟨hC_pos, ?_⟩

  intro a b n hign
  have hq_pos : (0 : ℝ) < q := by positivity
  have hq_ge_2 : (q : ℝ) ≥ 2 := by exact_mod_cast hq2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_n2_pos : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith : (1 : ℝ) < n + 2)
  have hlog_n2_ge_log2 : Real.log ((n : ℝ) + 2) ≥ Real.log 2 :=
    Real.log_le_log (by norm_num) (by linarith : (2 : ℝ) ≤ n + 2)

  -- Helper: log 2 > 1/2
  have hlog2_gt_half : Real.log 2 > 1/2 := by
    have hexp_half_lt : Real.exp (1/2) < 2 := by
      calc Real.exp (1/2) = Real.sqrt (Real.exp 1) := by rw [← Real.exp_half]
        _ ≤ Real.sqrt 3 := by apply Real.sqrt_le_sqrt; linarith [exp_one_lt_three]
        _ < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    rw [gt_iff_lt, Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)]
    exact hexp_half_lt

  -- log 2 < 1 since e > 2
  have hlog2_lt_1 : Real.log 2 < 1 := by
    have he_gt_2 : Real.exp 1 > 2 := exp_one_gt_two
    calc Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) he_gt_2
      _ = 1 := Real.log_exp 1

  -- Use Bertrand or exists_infinite_primes to get prime r > max(P, n)
  by_cases hmaxz : max P n = 0
  · -- max(P, n) = 0 means P = 0 and n = 0
    have hP0 : P = 0 := by simp only [Nat.max_eq_zero_iff] at hmaxz; exact hmaxz.1
    have hn0 : n = 0 := by simp only [Nat.max_eq_zero_iff] at hmaxz; exact hmaxz.2
    subst hP0 hn0
    have ha_lt : a < q := a_lt_large_prime a b 0 0 q hq_prime hq_gt (by omega) hign
    have hb_lt : b < q := b_lt_large_prime a b 0 0 q hq_prime hq_gt (by omega) hign
    have hab : (a : ℝ) + b < 2 * q := by exact_mod_cast (by omega : a + b < 2 * q)
    -- 2*q ≤ 20*q^2*log(2) for q ≥ 2 and log(2) > 0.5
    have h1 : (2 : ℝ) * q ≤ 20 * q^2 * Real.log 2 := by
      have h : (2 : ℝ) ≤ 10 * q := by nlinarith [hq_ge_2]
      nlinarith [sq_nonneg (q : ℝ), hlog2_gt_half, hq_ge_2]
    simp only [Nat.cast_zero, zero_add, Nat.cast_add]
    linarith

  · -- max(P, n) > 0
    have hmax_pos : 0 < max P n := Nat.pos_of_ne_zero hmaxz
    obtain ⟨r, hr_prime, hr_gt, hr_le⟩ := Nat.bertrand (max P n) (Nat.ne_of_gt hmax_pos)
    have hr_gt_P : r > P := Nat.lt_of_le_of_lt (le_max_left P n) hr_gt
    have hr_gt_n : r > n := Nat.lt_of_le_of_lt (le_max_right P n) hr_gt

    have ha_lt : a < r := a_lt_large_prime a b n P r hr_prime hr_gt_P hr_gt_n hign
    have hb_lt : b < r := b_lt_large_prime a b n P r hr_prime hr_gt_P hr_gt_n hign
    have hab_bound : a + b < 4 * max P n := by omega

    -- From key_ineq: a + b ≤ n + s_q(a) + s_q(b)
    have hconstr := hign q hq_prime hq_gt
    have hkey := key_ineq q a b n hconstr
    have hmax_le : max P n ≤ n + P := by simp [max_def]; split_ifs <;> omega

    -- Case 1: n ≤ P (small n case - constant bound)
    by_cases hnP : n ≤ P
    · have hmax_eq : max P n = P := max_eq_left hnP
      rw [hmax_eq] at hab_bound
      have hab_4P : (a : ℝ) + b < 4 * P := by exact_mod_cast hab_bound
      have hP_lt_q : (P : ℝ) < q := by exact_mod_cast hq_gt
      have h1 : (4 : ℝ) * P < 4 * q := by linarith
      -- 4*q ≤ 20*q^2*log(n+2) for q ≥ 2 and log(n+2) ≥ log(2) > 0.5
      have h2 : (4 : ℝ) * q ≤ 20 * q^2 * Real.log ((n : ℝ) + 2) := by
        have h : (4 : ℝ) ≤ 10 * q := by nlinarith [hq_ge_2]
        have hlog_ge_half : Real.log ((n : ℝ) + 2) > 1/2 := by linarith [hlog_n2_ge_log2, hlog2_gt_half]
        nlinarith [sq_nonneg (q : ℝ), hlog_ge_half, hq_ge_2]
      simp only [Nat.cast_add]; linarith

    · -- Case 2: n > P (use digit sum bound with logs)
      push_neg at hnP
      have hmax_eq : max P n = n := max_eq_right (le_of_lt hnP)
      rw [hmax_eq] at hab_bound hr_le

      have ha_lt_2n : a < 2 * n := by omega
      have hb_lt_2n : b < 2 * n := by omega
      have hn_pos : n ≥ 1 := by omega

      -- From hkey: a + b ≤ n + s_q(a) + s_q(b)
      have hkey_real : (a : ℝ) + b ≤ n + (Nat.digits q a).sum + (Nat.digits q b).sum := by
        have h : (a + b : ℕ) ≤ n + (Nat.digits q a).sum + (Nat.digits q b).sum := hkey
        exact_mod_cast h

      -- log(n+2) ≥ 1 since n+2 ≥ 3 > e
      have hlog_n2_ge_1 : Real.log ((n : ℝ) + 2) ≥ 1 := by
        have hn_real_ge_1 : (n : ℝ) ≥ 1 := by exact_mod_cast hn_pos
        have hn2_ge_3 : (n : ℝ) + 2 ≥ 3 := by linarith
        have he_lt_3 : Real.exp 1 < 3 := exp_one_lt_three
        have hlog3_gt_1 : Real.log (3 : ℝ) > 1 := by
          calc Real.log (3 : ℝ) > Real.log (Real.exp 1) :=
                Real.log_lt_log (Real.exp_pos 1) he_lt_3
            _ = 1 := Real.log_exp 1
        linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 3) hn2_ge_3]

      -- Bound digit sums
      have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1 : (1 : ℝ) < q)
      have hlogq_ge_log2 : Real.log (q : ℝ) ≥ Real.log 2 :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hq2 : (2 : ℝ) ≤ q)

      have hinv_log2_lt_2 : 1 / Real.log 2 < 2 := by
        rw [div_lt_iff₀ hlog2_pos]; linarith [hlog2_gt_half]

      have hlog_2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log n := by
        rw [Real.log_mul (by norm_num) (Nat.cast_pos.mpr hn_pos).ne']

      have hlog_n_le : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 2) := by
        apply Real.log_le_log (Nat.cast_pos.mpr hn_pos); linarith

      -- Bound digit sums
      have hsa_bound : ∀ m : ℕ, m ≠ 0 → m < 2 * n →
          ((Nat.digits q m).sum : ℝ) ≤ 5 * q * Real.log ((n : ℝ) + 2) := by
        intro m hm0 hm_lt
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
        have hsm := digit_sum_bound q m hq1 hm0
        have hsm_real' : ((Nat.digits q m).sum : ℝ) ≤ ((q : ℝ) - 1) * ((Nat.log q m : ℝ) + 1) := by
          have h1 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
            have hq2' : (1 : ℕ) ≤ q := by omega
            simp [Nat.cast_sub hq2']
          have h2 : ((Nat.log q m + 1 : ℕ) : ℝ) = (Nat.log q m : ℝ) + 1 := by push_cast; ring
          calc ((Nat.digits q m).sum : ℝ)
              ≤ ((q - 1 : ℕ) * (Nat.log q m + 1 : ℕ) : ℕ) := by exact_mod_cast hsm
            _ = ((q - 1 : ℕ) : ℝ) * ((Nat.log q m + 1 : ℕ) : ℝ) := by push_cast; ring
            _ = ((q : ℝ) - 1) * ((Nat.log q m : ℝ) + 1) := by rw [h1, h2]

        have hlog_m := nat_log_le_real_log_div q m hq1 hm_pos
        have hlog_m_bound : Real.log (m : ℝ) < Real.log (2 * n) := by
          apply Real.log_lt_log (Nat.cast_pos.mpr hm_pos)
          have h : (m : ℝ) < 2 * n := by exact_mod_cast hm_lt
          linarith

        have hlog_m_bound' : Real.log (m : ℝ) < 1 + Real.log ((n : ℝ) + 2) := by
          calc Real.log (m : ℝ) < Real.log (2 * n) := hlog_m_bound
            _ = Real.log 2 + Real.log n := hlog_2n
            _ < 1 + Real.log n := by linarith [hlog2_lt_1]
            _ ≤ 1 + Real.log ((n : ℝ) + 2) := by linarith [hlog_n_le]

        have hlog_m_nonneg : 0 ≤ Real.log (m : ℝ) := by
          apply Real.log_nonneg; exact_mod_cast hm_pos

        have hnatlog_bound : (Nat.log q m : ℝ) < 2 + 2 * Real.log ((n : ℝ) + 2) := by
          calc (Nat.log q m : ℝ)
              ≤ Real.log m / Real.log q := hlog_m
            _ ≤ Real.log m / Real.log 2 := by
                apply div_le_div_of_nonneg_left hlog_m_nonneg hlog2_pos hlogq_ge_log2
            _ < (1 + Real.log ((n : ℝ) + 2)) / Real.log 2 := by
                apply div_lt_div_of_pos_right hlog_m_bound' hlog2_pos
            _ = 1 / Real.log 2 + Real.log ((n : ℝ) + 2) / Real.log 2 := by ring
            _ < 2 + Real.log ((n : ℝ) + 2) / Real.log 2 := by linarith [hinv_log2_lt_2]
            _ < 2 + 2 * Real.log ((n : ℝ) + 2) := by
                have h : Real.log ((n : ℝ) + 2) / Real.log 2 < 2 * Real.log ((n : ℝ) + 2) := by
                  rw [div_lt_iff₀ hlog2_pos]
                  nlinarith [hlog_n2_pos, hlog2_gt_half]
                linarith

        -- s_q(m) ≤ (q-1)*(Nat.log q m + 1) < (q-1)*(3+2*log(n+2)) ≤ q*(3+2*log(n+2)) ≤ 5*q*log(n+2)
        have h_step1 : ((Nat.digits q m).sum : ℝ) < (q - 1) * (3 + 2 * Real.log ((n : ℝ) + 2)) := by
          have h : (q - 1 : ℝ) > 0 := by linarith [hq_ge_2]
          calc ((Nat.digits q m).sum : ℝ)
              ≤ (q - 1) * ((Nat.log q m : ℝ) + 1) := hsm_real'
            _ < (q - 1) * (3 + 2 * Real.log ((n : ℝ) + 2)) := by nlinarith [hnatlog_bound, h]
        have h_step2 : (q - 1 : ℝ) * (3 + 2 * Real.log ((n : ℝ) + 2)) ≤ q * (3 + 2 * Real.log ((n : ℝ) + 2)) := by
          have h1 : (3 : ℝ) + 2 * Real.log ((n : ℝ) + 2) > 0 := by linarith [hlog_n2_pos]
          nlinarith
        have h_step3 : (q : ℝ) * (3 + 2 * Real.log ((n : ℝ) + 2)) ≤ q * (5 * Real.log ((n : ℝ) + 2)) := by
          have h : (3 : ℝ) + 2 * Real.log ((n : ℝ) + 2) ≤ 5 * Real.log ((n : ℝ) + 2) := by
            nlinarith [hlog_n2_ge_1]
          nlinarith [hq_pos]
        linarith

      -- Apply the bound to a and b
      by_cases ha0 : a = 0
      · subst ha0
        simp only [Nat.digits_zero, List.sum_nil, Nat.cast_zero, zero_add] at hkey_real ⊢
        by_cases hb0 : b = 0
        · subst hb0; simp; positivity
        · have hsb := hsa_bound b hb0 hb_lt_2n
          have hkey' : (b : ℝ) ≤ n + (Nat.digits q b).sum := by linarith
          -- 5*q ≤ 20*q^2 for q ≥ 1
          have h5q : (5 : ℝ) * q ≤ 20 * q^2 := by nlinarith [sq_nonneg (q : ℝ), hq_ge_2]
          calc (b : ℝ)
              ≤ n + (Nat.digits q b).sum := hkey'
            _ ≤ n + 5 * q * Real.log ((n : ℝ) + 2) := by linarith [hsb]
            _ ≤ n + 20 * q^2 * Real.log ((n : ℝ) + 2) := by nlinarith [hlog_n2_pos, h5q]

      · by_cases hb0 : b = 0
        · subst hb0
          simp only [Nat.digits_zero, List.sum_nil, Nat.cast_zero, add_zero] at hkey_real ⊢
          have hsa := hsa_bound a ha0 ha_lt_2n
          have h5q : (5 : ℝ) * q ≤ 20 * q^2 := by nlinarith [sq_nonneg (q : ℝ), hq_ge_2]
          calc (a : ℝ)
              ≤ n + (Nat.digits q a).sum := hkey_real
            _ ≤ n + 5 * q * Real.log ((n : ℝ) + 2) := by linarith [hsa]
            _ ≤ n + 20 * q^2 * Real.log ((n : ℝ) + 2) := by nlinarith [hlog_n2_pos, h5q]

        · have hsa := hsa_bound a ha0 ha_lt_2n
          have hsb := hsa_bound b hb0 hb_lt_2n
          have h10q : (10 : ℝ) * q ≤ 20 * q^2 := by nlinarith [sq_nonneg (q : ℝ), hq_ge_2]
          simp only [Nat.cast_add]
          calc (a : ℝ) + b
              ≤ n + (Nat.digits q a).sum + (Nat.digits q b).sum := hkey_real
            _ ≤ n + 5 * q * Real.log ((n : ℝ) + 2) + 5 * q * Real.log ((n : ℝ) + 2) := by linarith [hsa, hsb]
            _ = n + 10 * q * Real.log ((n : ℝ) + 2) := by ring
            _ ≤ n + 20 * q^2 * Real.log ((n : ℝ) + 2) := by nlinarith [hlog_n2_pos, h10q]
