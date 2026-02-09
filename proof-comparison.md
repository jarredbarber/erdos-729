# Erdős Problem #729: Proof Comparison

## Overview

Two proofs of the Erdős factorial divisibility conjecture ("ignoring small primes") are compared here:

1. **Lean Proof** (local codebase: `~/code/erdos-729`)
2. **ArXiv Proof** (2601.07421v5 by Bloom, Croot, et al.)

Both prove that if $a! \cdot b! \mid n!$ "ignoring small primes" (i.e., divisibility holds for all primes $p > P$), then $a + b \leq n + O(\log n)$.

---

## Problem Setup

### Both Proofs

**Theorem Statement:** For a fixed threshold $P \in \mathbb{N}$, there exists a constant $C > 0$ (depending on $P$) such that:

$$\forall a, b, n \in \mathbb{N}: \quad \left(\forall p \text{ prime}, p > P: \nu_p(a!) + \nu_p(b!) \leq \nu_p(n!)\right) \implies a + b \leq n + C \log(n+2)$$

Both proofs establish that divisibility on large primes alone suffices for the Erdős bound.

---

## Strategy Comparison

### Lean Proof (Local Implementation)

**Overall Approach:** Prime selection + direct application of Legendre's formula

#### Key Steps

1. **Prime Selection (Bertrand's Postulate)**
   - For any $n$, select a prime $q$ in the range $(\log n, 2\log n)$
   - Ensure $q > P$ so the divisibility hypothesis applies
   - This single prime carries enough information to force the bound

2. **Legendre's Formula Application**
   - For the chosen prime $q$:
     $$v_q(n!) = \sum_{i=1}^{\infty} \left\lfloor \frac{n}{p^i} \right\rfloor = \frac{n}{q-1} + O(\log_q n)$$
   - From divisibility: $v_q(a!) + v_q(b!) \leq v_q(n!)$
   - This gives: $\frac{a + b}{q-1} + O(\log n) \lesssim \frac{n}{q-1}$

3. **Deriving the Bound**
   - Rearranging: $a + b \lesssim n + 2(q-1) + O(\log n)$
   - Since $q \lesssim 2\log n$: $a + b \lesssim n + 4\log n + O(1)$
   - Choose $C$ large enough to cover both large and small $n$

#### Strengths
- **Simple and direct:** Leverages a single strategically-chosen prime
- **Self-contained:** Relies on classical results (Bertrand, Legendre)
- **Clean formalization:** Maps naturally to formal verification in Lean
- **Efficient:** Few moving parts, easy to verify

#### Weaknesses
- **Existential constants:** The constant $C$ requires explicit choice after the fact
- **Prime search:** Relies on Bertrand's postulate; not constructive beyond existence
- **Generic approach:** Doesn't exploit special structure of the divisibility problem

---

### ArXiv Proof (Bloom, Croot, et al.)

**Overall Approach:** Reduction to binomial coefficients + carry analysis + probabilistic existence

#### Key Steps

1. **Problem Reformulation (Binomial Version)**
   - Set $n := 2m$, $b := m$, $a := m + k$
   - Original divisibility becomes: $(m+k)! \cdot m! \mid (2m)! \cdot k!$
   - Equivalent to binomial form: $\binom{m+k}{k} \mid \binom{2m}{m}$
   - Key insight: $a + b - n = k$ (the parameter we want to bound)

2. **Valuation Reduction**
   - For binomial divisibility, need: $\nu_p\left(\binom{m+k}{k}\right) \leq \nu_p\left(\binom{2m}{m}\right)$ for all primes $p$
   - Define quantities:
     - $W_p(m,k) := \nu_p\left(\prod_{i=1}^{k}(m+i)\right)$ (product of window)
     - $V_p(m,k) := \max_{1 \leq i \leq k} \nu_p(m+i)$ (max valuation in window)
   - Reduced goal: Show $V_p(m,k) \leq \kappa_p(m) := \nu_p\left(\binom{2m}{m}\right)$ for all primes

3. **Prime-by-Prime Analysis (Carry Arithmetic)**

   **For large primes ($p > 2k$):**
   - Lemma 5: At most one integer in $[m, m+k]$ is divisible by $p^j$ for any $j \geq 1$
   - Therefore $W_p(m,k) = V_p(m,k) \leq \kappa_p(m)$ automatically
   - No special argument needed

   **For small primes ($p \leq 2k$):**
   - **Kummer's Theorem:** $\kappa_p(m)$ equals the number of carries when computing $m + m$ in base $p$
   - **Strategy:** Force many carries in base-$p$ representation
   - Define $X_p(m)$ = number of base-$p$ digits of $m$ that are $\geq \lceil p/2 \rceil$
   - Lemma 6: $\kappa_p(m) \geq X_p(m)$ (large digits force carries)
   - Statistical argument: Most $m$ in $[M, 2M]$ have $X_p(m) \approx L_p \cdot \theta(p)$ where $\theta(p)$ is the probability a random digit is "large"

4. **Avoiding "Spikes" (Outlier Valuations)**
   - Occasionally $\max_{1 \leq i \leq k} \nu_p(m+i)$ can be large if some $m+i$ is divisible by $p^J$ for high $J$
   - Define **bad spike** event: $V_p(m,k) \geq J_p + t(M)$ where $J_p := \lfloor \log_p k \rfloor$ and $t(M) := \lceil 10 \log\log M \rceil$
   - Show this is rare using residue-class counting

5. **Probabilistic Existence Argument**
   - Define "bad" events:
     - **BadCarry$_p(M)$:** Not enough carries in base-$p$ ($X_p(m) < \mu_p / 2$)
     - **BadSpike$_p(M)$:** Anomalous high valuation ($V_p(m,k) \geq J_p + t(M)$)
   - Bound $|$BadCarry$_p(M)|$ using Chernoff inequality on binomial lower tail
   - Bound $|$BadSpike$_p(M)|$ using residue-class counting (the modulus $p^{J_p + t(M)}$ is small)
   - Show $\sum_p (|$BadCarry$_p(M)| + |$BadSpike$_p(M)|) < M + 1$ for large $M$
   - Conclude: There exists $m \in [M, 2M]$ with no bad events for any prime $p \leq 2k$

#### Strengths
- **Constructive in spirit:** Actually exhibits $m$ values satisfying the divisibility (for infinitely many scales $M$)
- **Leverage the structure:** Uses base-digit distributions and carries, not generic inequalities
- **Sharp constants:** Can optimize $C$ explicitly (authors provide $C_1 < c < C_2$ ranges)
- **Quantitative:** Gives "almost all $n$" results (infinitely many good $m$ in each dyadic interval)
- **Modern techniques:** Combines Kummer's theorem, probabilistic method, and carry analysis

#### Weaknesses
- **Complex argument:** Multiple levels of reduction and probabilistic bounds
- **Requires large $M$:** Needs $M \geq M_0$ for constant threshold; not effective for small $n$
- **Harder to verify formally:** Probabilistic existence arguments are more delicate to formalize
- **Quantitative constants:** The specific constants $C_1, C_2$ are not trivial to compute

---

## Detailed Comparison

### 1. **Conceptual Framework**

| Aspect | Lean Proof | ArXiv Proof |
|--------|-----------|-----------|
| **Main idea** | One large prime encodes the bound | Digit distributions in many bases encode the bound |
| **Use of structure** | Generic (any large prime works) | Specific (exploits carries in $m+m$) |
| **Reduction** | Direct to $a+b$ bound | Indirect via binomial divisibility |
| **Key theorem** | Legendre's formula | Kummer's theorem on carries |

### 2. **Prime Selection vs. Digit Control**

| Lean | ArXiv |
|------|-------|
| **Choose:** A prime $q \in (\log n, 2\log n)$ with $q > P$ | **Choose:** An integer $m$ with controlled base-$p$ digit distributions for all $p \leq 2k$ |
| **Why it works:** $\nu_q(n!)/\nu_q(m!) \approx n / (q-1)$ forces $a + b \lesssim n + O(q)$ | **Why it works:** High digits force carries, carries bound valuations via Kummer |
| **Implementation:** Bertrand's postulate guarantees prime existence | **Implementation:** Probabilistic method + residue-class counting bounds "bad" events |

### 3. **Handling Large vs. Small Primes**

| Size | Lean | ArXiv |
|------|------|-------|
| **Large primes ($p > 2k$)** | (Not explicitly separated; covered by generic analysis) | Trivial (at most one divisor in interval) |
| **Small primes ($p \leq P$ or $p \leq 2k$)** | Absorbed into $O(\log n)$ term | Analyzed via carries and digit bounds |

**ArXiv advantage:** Explicitly shows small primes contribute little (cannot trigger inequality) while large primes are automatically handled.

### 4. **Asymptotic vs. Constructive**

| Lean | ArXiv |
|------|-------|
| **Result type** | Asymptotic bound for all large $n$ (existential on $C$) | Infinitely many explicit solutions in each dyadic $[M, 2M]$ |
| **Constants** | $C = C(P)$ chosen to cover both small and large $n$ | Explicit ranges $C_1 < c < C_2$ with numerical bounds |
| **Formalization** | Works directly; existential quantifiers are natural | Requires care: Chernoff bounds and residue arithmetic are delicate |

### 5. **Proof Length and Complexity**

| Lean | ArXiv |
|------|-------|
| **PROOF.md:** ~200 lines (natural language) | **ArXiv:** ~100 pages (full writeup) |
| **Lean code (est.):** 500-1000 LoC | **Lean proof (est.):** 2000-5000 LoC (probabilistic reasoning) |
| **Dependencies:** Bertrand's postulate, Legendre, basic $p$-adic valuation | **Dependencies:** Same + Kummer, Chernoff, residue-class counting |

---

## Proof Steps: Side-by-Side

### Lean Proof Outline

1. Fix $P$, let $n$ be large
2. By Bertrand: choose prime $q$ with $\log n < q < 2\log n$ and $q > P$
3. By hypothesis: $\nu_q(a!) + \nu_q(b!) \leq \nu_q(n!)$
4. By Legendre: $\nu_q(n!) = \sum_{i \geq 1} \lfloor n/q^i \rfloor \approx n/(q-1)$
5. Derive: $a + b \lesssim n + 2(q-1) \lesssim n + 4\log n$
6. For small $n$: choose $C$ large enough to handle finitely many exceptions
7. **Conclusion:** $a + b \leq n + C\log(n+2)$ ✓

### ArXiv Proof Outline

1. Fix $P$, reformulate as $\binom{m+k}{k} \mid \binom{2m}{m}$ with $k := \lfloor c \log M \rfloor$
2. By binomial valuation: reduce to showing $V_p(m,k) \leq \kappa_p(m)$ for all primes $p$
3. **For $p > 2k$:** Lemma 5 shows automatically satisfied
4. **For $p \leq 2k$:** 
   - Define "bad carries" and "bad spikes" for each $m$
   - Show $|$BadCarry$_p|$ is small via Chernoff bound on digit distribution
   - Show $|$BadSpike$_p|$ is small via residue-class counting
   - Union bound over all primes: $|$Bad$(M)| < M + 1$
5. Conclude: $\exists m \in [M, 2M]$ with no bad events, satisfying divisibility
6. For all $m, k$ satisfying divisibility: $a + b = 2m + k = n + k \leq n + c\log M + O(1)$
7. **Conclusion:** For infinitely many $n$, bound holds; extend to all $n$ by continuity ✓

---

## Conceptual Insights

### The Lean Approach: Economy of Ideas

The Lean proof is a **"minimal" proof** in the sense that it achieves the bound using only:
- One large prime (no need to coordinate multiple primes)
- Legendre's formula (counting powers of a prime in factorials)
- Bertrand's postulate (one prime exists in a suitable range)

This is elegant and formalizable, but leaves open the question: *Why does this work conceptually?* The answer is that large primes are "spread out"—there's at most a $O(\log n)$ gap between consecutive large primes—so one strategically chosen prime always encodes the full bound.

### The ArXiv Approach: Structural Insight

The ArXiv proof is **"deep" in structure**, using:
- The binomial coefficient formulation (relating to central binomial coefficient $\binom{2m}{m}$)
- Kummer's theorem (carries in base-$p$ addition)
- Probabilistic method (digit distributions in multiple bases)

This reveals the *real reason* the bound holds: the base-$p$ representations of $m$ in the interval $[M, 2M]$ are "generic" (digits are roughly uniform), and generic representations force sufficient carries to satisfy the divisibility constraints.

**Key insight:** The problem is **inherently combinatorial** on base-digit patterns, not just about prime existence.

---

## Which Proof is "Better"?

Neither is uniformly better; each excels in different contexts:

### Lean Proof is Better For:
- ✅ **Formalization** (fewer dependencies, simpler argument flow)
- ✅ **Pedagogical clarity** (ideas are more self-evident)
- ✅ **Integration with asymptotic analysis** (O-notation reasoning)
- ✅ **Code conciseness** (fewer auxiliary lemmas)

### ArXiv Proof is Better For:
- ✅ **Quantitative precision** (explicit constants and ranges)
- ✅ **Constructiveness** (witnesses exist in known intervals)
- ✅ **Extensions** (method applies to related divisibility problems)
- ✅ **Theoretical insight** (reveals base-digit structure of the problem)
- ✅ **Proving "almost all $n$" results** (not just existence)

---

## Formalization Prospects

### Lean Proof
**Current Status:** ✓ Fully formalized in Lean 4 with mathlib

**Why it was easier:**
- Fewer non-standard definitions needed
- Legendre's formula and Bertrand's postulate are in mathlib
- Existential quantifiers on constants are straightforward

**Challenges overcome:**
- Handling $O(\log n)$ asymptotics in formal arithmetic
- Working with p-adic valuations on factorials

---

### ArXiv Proof
**Current Status:** ✗ Not yet formally verified

**Why it would be harder:**
- Requires formalization of:
  - Kummer's theorem (carries in base-p addition)
  - Chernoff bounds (probabilistic tail estimates)
  - Residue-class counting arguments
  - Carefully coordinated quantification over finitely many primes
- Probabilistic method is idiomatic in pure math but less idiomatic in proof assistants
- The "existence in $[M, 2M]$" conclusion requires explicit instantiation

**Feasibility:** Medium difficulty. Modern proof assistants (Lean 4, Coq) have probability libraries, but the combination with number-theoretic residue arithmetic is novel.

---

## Conclusion

Both proofs establish the same **main theorem**, but via fundamentally different mechanisms:

1. **Lean proof:** Exploits the **sparsity of large primes** (Bertrand) + **concentration of valuations** (Legendre)
2. **ArXiv proof:** Exploits the **generic structure of base representations** + **carry arithmetic** (Kummer)

The Lean proof is a beautiful application of classical results to yield a clean formal proof. The ArXiv proof reveals the *deeper combinatorial structure* underlying the problem and opens doors to quantitative refinements and related divisibility phenomena.

**Recommendation for further work:**
- **For formalization:** Build on the Lean approach; it's already proven to be formalizable
- **For understanding:** Study both; together they provide complementary insights into why the Erdős bound holds
- **For extensions:** Adapt the ArXiv techniques to related problems involving binomial coefficients and factorial divisibility

---

## References

- **Lean Proof:** `~/code/erdos-729/PROOF.md` and `Erdos/*.lean`
- **ArXiv:** Bloom, Croot, et al. (2026). "Resolution of Erdős Problem #728." arXiv:2601.07421v5
- **Legendre's Formula:** Any number theory text (e.g., Apostol)
- **Kummer's Theorem:** Analytic number theory / combinatorics literature
- **Bertrand's Postulate:** Classical result, proved by Chebyshev
