# Erdős Factorial Divisibility Theorem (Ignoring Small Primes)

A formal Lean 4 proof of an Erdős conjecture about factorial divisibility.

## The Problem

Erdős proved that if a!b! | n! then a+b ≤ n + O(log n). This project proves the generalization: the same bound holds even if we only require divisibility "ignoring small primes."

## What divisibility of factorials means

**a!b! | n!** means n! / (a!·b!) is an integer. For example:
- 2!·3! | 5! because 5! / (2!·3!) = 120 / (2·6) = 10 ✓
- 3!·3! | 5! because 5! / (3!·3!) = 120 / (6·6) = 3.33... ✗

## The p-adic valuation connection

The **fundamental theorem of arithmetic** says every integer factors uniquely into primes. So to check if A divides B, you just check: for every prime p, does p appear at least as many times in B as in A?

The **p-adic valuation** v_p(n) counts how many times prime p divides n. For example:
- v_2(12) = 2 because 12 = 2² · 3
- v_3(12) = 1

So **A | B** if and only if **v_p(A) ≤ v_p(B) for every prime p**.

Applied to factorials: **a!b! | n!** ⟺ **v_p(a!) + v_p(b!) ≤ v_p(n!) for all primes p**.

(The left side uses v_p(a!·b!) = v_p(a!) + v_p(b!) since v_p is additive for multiplication.)

## What "ignoring small primes" means

The original Erdős result: if the divisibility holds for ALL primes, then a+b ≤ n + O(log n).

The extended conjecture asks: what if we only require it for primes p > P (ignoring the small ones ≤ P)?

So the Lean statement:
```lean
∀ p : ℕ, p.Prime → p > P →
    padicValNat p a.factorial + padicValNat p b.factorial ≤ padicValNat p n.factorial
```

is literally saying: "for all primes p bigger than P, v_p(a!) + v_p(b!) ≤ v_p(n!)." That's exactly "a!b! | n! ignoring primes ≤ P."

## The Lean theorem

```lean
def IgnoresSmallPrimes (a b n P : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p > P →
    padicValNat p a.factorial + padicValNat p b.factorial ≤
    padicValNat p n.factorial

theorem erdos_factorial_ignoring_small_primes (P : ℕ) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (a b n : ℕ),
      IgnoresSmallPrimes a b n P →
      ((a + b : ℕ) : ℝ) ≤ (n : ℝ) + C * Real.log ((n : ℝ) + 2)
```

For any threshold P, there's a constant C (depending on P) such that a+b ≤ n + C·log(n+2). The C grows with P (it's 20q² where q is the first prime after P), which makes sense — the more primes you ignore, the weaker your hypothesis, so the constant gets worse. But it's still O(log n).

The use of log(n+2) instead of log(n) avoids undefined log(0) and ensures the bound works for n=0,1. Since log(n+2) = Θ(log n) for large n, this is a standard formalization choice.

## Proof strategy

1. **Legendre's formula**: (p-1)·v_p(n!) = n - s_p(n), where s_p(n) is the digit sum of n in base p
2. **Key inequality**: From the divisibility hypothesis, a + b ≤ n + s_q(a) + s_q(b) for any prime q > P
3. **Bertrand's postulate**: Gives a crude bound a, b < 2n (by finding a prime between n and 2n)
4. **Digit sum bound**: s_q(m) ≤ (q-1)·(log_q(m) + 1), and with m < 2n this gives s_q(m) ≤ 5q·log(n+2)
5. **Combine**: a + b ≤ n + 10q·log(n+2) ≤ n + 20q²·log(n+2)

## Verification

```bash
lake build                                    # Build completed successfully
grep -rn "sorry" Erdos/ --include="*.lean"    # No sorrys
```

## Success criteria

| Criterion | Status |
|-----------|--------|
| Theorem statement matches problem, no extra assumptions | ✅ |
| `lake build` succeeds | ✅ |
| No sorrys in codebase | ✅ |
