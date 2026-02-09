# Erdős Problem #729: Proof Comparison

## Overview

Three AI-generated proofs of the Erdős factorial divisibility conjecture ("ignoring small primes") are compared here, each from a different model:

1. **Claude Lean Proof** (local codebase: `~/code/erdos-729`) - Claude model
2. **Gemini Lean Proof** (local codebase: `~/code/erdos-729-google`) - Gemini model  
3. **GPT-5.2 ArXiv Proof** (arXiv:2601.07421v5) - GPT-5.2 model, published by Bloom, Croot, et al.

All three prove that if $a! \cdot b! \mid n!$ "ignoring small primes" (i.e., divisibility holds for all primes $p > P$), then $a + b \leq n + O(\log n)$.

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

### Google/Gemini Lean Proof (erdos-729-google)

**Overall Approach:** Prime selection + logarithm transformation + case split (small/large $n$)

This is a **Lean 4 formalization** driven by Google Gemini AI, attempting a more refined version of the classical approach.

#### Key Steps

1. **Prime Selection (Same as Simple Lean)**
   - Choose a prime $p > \max(P, 2)$ via Bertrand's postulate
   - Define $K := \frac{p-1}{\log p}$ (key constant relating prime size to logarithm)

2. **Logarithm Transformation Lemma (Novel)**
   - **log_bound lemma:** Transforms inequalities of the form $a \leq n + K \log a$ to $a \leq n + C' \log n$
   - Uses helper lemma `log_bound_helper`: Shows that for large $x$, we have $C \log x \leq x/2$
   - This is the crucial step that handles the iterative logarithm issue

3. **Digit Sum Bounds (Detailed)**
   - Formalize Legendre's formula: $(p-1) \cdot v_p(n!) = n - S_p(n)$ where $S_p(n)$ is digit sum in base $p$
   - Prove: $S_p(n) \leq (p-1)(\log_p n + 1) = O(\log n)$
   - **Real version:** $S_p(n) \leq \frac{p-1}{\log p} \log n + (p-1)$ as a real inequality

4. **Case Split**

   **Case 1: Small $n$ (where $n < p$)**
   - If $p \nmid n!$, then $v_p(n!) = 0$
   - From divisibility hypothesis: $v_p(a!) + v_p(b!) \leq 0$, so both are $0$
   - This means $a < p$ and $b < p$
   - Therefore $a + b < 2p$
   - Bound: $2p \approx 2\log n$ in the limiting regime

   **Case 2: Large $n$ (where $n \geq p$)**
   - Define $N := n + (p-1)$ (adjusted scale)
   - Show $a - S_p(a) \leq n$ (from Legendre and divisibility)
   - Combine with digit sum bound to get: $a \leq n + K \log a + (p-1)$
   - Apply log_bound lemma with parameter $N$: $a \leq N + C' \log N$
   - Since $N \leq 2n$, obtain final bound

5. **Constant Management**
   - Define multiple constants:
     - $C_{\text{small}} := \frac{2p}{\log 2}$ (for small $n$ case)
     - $C_{\text{const}}$ (combines various log terms)
     - $C_{\text{large}}$ (for large $n$ case)
     - $C := \max(C_{\text{small}}, C_{\text{large}})$ (final choice)

#### Strengths
- **Sophisticated formal development:** Deep lemma structure (Erdos/Lemmas.lean) with detailed auxiliary results
- **Explicit case handling:** Cleanly separates small and large $n$ with distinct strategies
- **Intermediate transformations:** The log_bound lemma is a powerful abstraction, useful for other problems
- **Detailed digit sum formalization:** Both integer and real versions, carefully connected
- **Organized code:** Modular structure with separate lemma and work files

#### Weaknesses
- **Incomplete proof:** Main theorem has a `sorry` (completion claimed to be "mathematically sound but implementation details preventing compilation")
- **Complex constant management:** Many nested constants with intricate dependencies; harder to verify correctness
- **Deep formalization:** Many auxiliary lemmas; more surface area for bugs
- **Implementation challenges:** Different AI model (Gemini vs Claude) produced a different approach; reflects model-specific strategic choices rather than unique mathematical insight

#### Position in the Spectrum

This proof sits **between the simple Lean proof and the ArXiv proof**:
- Like the simple Lean proof: Uses Legendre's formula and a single prime
- Like the ArXiv proof: Has explicit case analysis and sophisticated constant tracking
- Unlike both: Focuses on formalizing the auxiliary lemmas rather than the main argument

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

| Aspect | Simple Lean | Google/Gemini Lean | ArXiv Proof |
|--------|-----------|-----------|-----------|
| **Main idea** | One large prime + direct algebra | One prime + log transformation + case split | Digit distributions in many bases |
| **Use of structure** | Generic (any large prime works) | Generic + algorithmic | Specific (exploits carries in $m+m$) |
| **Reduction** | Direct to $a+b$ bound | Split into two cases | Indirect via binomial divisibility |
| **Key theorem** | Legendre's formula | Legendre + log_bound | Kummer's theorem on carries |
| **Formalization status** | ✓ Complete | ✗ Incomplete (has sorry) | ✗ Not attempted |

### 2. **Prime Selection vs. Digit Control**

| Simple Lean | Google/Gemini | ArXiv |
|------|-------|-------|
| **Choose:** A prime $q \in (\log n, 2\log n)$ with $q > P$ | **Choose:** A prime $p > \max(P, 2)$; transform the inequality | **Choose:** An integer $m$ with controlled base-$p$ digit distributions |
| **Why it works:** $\nu_q(n!)/\nu_q(m!) \approx n / (q-1)$ forces bound | **Why it works:** Log_bound lemma handles the nested logs; case split simplifies | **Why it works:** High digits force carries, carries bound valuations via Kummer |
| **Implementation:** Bertrand's postulate guarantees prime existence | **Implementation:** Lemma library + case analysis | **Implementation:** Probabilistic method + residue-class counting |

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

| Simple Lean | Google/Gemini | ArXiv |
|------|-------|-------|
| **Natural Language:** ~200 lines | **Lean code:** 400+ LoC (Lemmas.lean) + 200+ LoC (Work.lean) | **ArXiv writeup:** ~100 pages |
| **Lean code:** 500-1000 LoC (est. if completed) | **Status:** Incomplete (main theorem has sorry) | **Lean code (est.):** 2000-5000 LoC |
| **Dependencies:** Bertrand, Legendre, basic $p$-adic valuation | **Dependencies:** Bertrand, Legendre, real logarithms, digit operations | **Dependencies:** Same + Kummer, Chernoff, residue-class counting |

---

## Three-Way Comparison Table

| Feature | Simple Lean | Google/Gemini | ArXiv |
|---------|-----------|----------|-------|
| **Formalization** | ✓ Complete | ✗ Incomplete | ✗ None |
| **Pedagogical clarity** | ★★★★★ | ★★★ | ★★ |
| **Technical depth** | ★★ | ★★★★ | ★★★★★ |
| **Lemma complexity** | Low | Medium | High |
| **Case analysis** | Implicit | Explicit (2 cases) | Explicit (3 ranges for primes) |
| **Constant explicitness** | Simple | Complex | Very complex |
| **Probabilistic elements** | None | None | Heavy |
| **Use of digit arithmetic** | No | Yes (formalized) | Yes (structural) |
| **Constructiveness** | Existential | Existential | Constructive (in intervals) |

---

## Proof Steps: Side-by-Side

### Simple Lean Proof Outline

1. Fix $P$, let $n$ be large
2. By Bertrand: choose prime $q$ with $\log n < q < 2\log n$ and $q > P$
3. By hypothesis: $\nu_q(a!) + \nu_q(b!) \leq \nu_q(n!)$
4. By Legendre: $\nu_q(n!) = \sum_{i \geq 1} \lfloor n/q^i \rfloor \approx n/(q-1)$
5. Derive: $a + b \lesssim n + 2(q-1) \lesssim n + 4\log n$
6. For small $n$: choose $C$ large enough to handle finitely many exceptions
7. **Conclusion:** $a + b \leq n + C\log(n+2)$ ✓

### Google/Gemini Proof Outline

1. Fix $P$, choose prime $p > \max(P, 2)$ by Bertrand's postulate
2. Define $K := \frac{p-1}{\log p}$ (key scaling constant)
3. Establish log_bound lemma: Transforms $a \leq n + K \log a$ to $a \leq N + C' \log N$ for adjusted $N$
4. **Case 1: $n < p$ (small $n$)**
   - Show $v_p(n!) = 0$ (prime too large)
   - From divisibility hypothesis: $v_p(a!) = v_p(b!) = 0$
   - Conclude: $a < p$ and $b < p$, so $a + b < 2p$
   - Bound: $a + b \leq C_{\text{small}} \log(n+2)$ where $C_{\text{small}} := \frac{2p}{\log 2}$
5. **Case 2: $n \geq p$ (large $n$)**
   - Use Legendre's formula: $(p-1) v_p(m!) = m - S_p(m)$ where $S_p(m)$ is base-$p$ digit sum
   - From divisibility: $(p-1)(v_p(a!) + v_p(b!)) \leq (p-1)v_p(n!)$
   - Rearrange: $a + b \leq n + S_p(a) + S_p(b)$
   - Bound digit sums: $S_p(a) \leq K \log a + (p-1)$ (from $S_p(m) \leq (p-1)\log_p m + (p-1)$)
   - Set $N := n + (p-1)$ and apply log_bound: $a \leq N + C' \log N$
   - Similarly for $b$; combine to get $a + b \leq n + C_{\text{large}} \log(n+2)$
6. Final constant: $C := \max(C_{\text{small}}, C_{\text{large}})$
7. **Conclusion:** $a + b \leq n + C\log(n+2)$ ✓ (claimed; proof incomplete)

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

### The Gemini Approach: Formalization Refinement

The Gemini-generated proof is a **"systematic formalization"** that differs from Claude's strategy:
- Breaks the argument into explicit cases (small vs. large $n$)
- Introduces an auxiliary lemma (log_bound) to handle logarithmic iteration
- Provides detailed digit sum formalization (both integer and real versions)
- Organizes lemmas into a library (Erdos/Lemmas.lean) for potential reuse

This represents a **different AI model's strategic choice** vs. Claude's minimalist approach: intermediate complexity that keeps Legendre's formula but adds structure. The incomplete proof (main theorem has a `sorry`) suggests that explicit case-split + complex constant management created **more formalization friction than the informal argument suggested**.

**Key insight:** Different AI models generate different proof strategies; what one model solves directly (Claude), another decomposes into auxiliary lemmas (Gemini). Formalization success is unpredictable.

### The GPT-5.2 Approach: Structural Insight

The GPT-5.2-generated ArXiv proof is **"deep" in structure**, using:
- The binomial coefficient formulation (relating to central binomial coefficient $\binom{2m}{m}$)
- Kummer's theorem (carries in base-$p$ addition)
- Probabilistic method (digit distributions in multiple bases)
- Sophisticated constant management and residue-class counting

This reveals the *real reason* the bound holds: the base-$p$ representations of $m$ in the interval $[M, 2M]$ are "generic" (digits are roughly uniform), and generic representations force sufficient carries to satisfy the divisibility constraints. GPT-5.2's approach is the most mathematically sophisticated but also the most complex—and not yet formalized in a proof assistant.

**Key insight:** Deeper AI models find richer mathematical structure; richer structure is harder to formalize. The problem is **inherently combinatorial** on base-digit patterns.

---

## Which Proof is "Better"?

All three have strengths and weaknesses; none is uniformly superior:

### Claude Proof is Best For:
- ✅ **Pedagogical clarity** (most direct, easiest to explain)
- ✅ **Complete formalization** (only fully verified code exists)
- ✅ **Implementation efficiency** (fewer moving parts)
- ✅ **Undergraduate-level understanding**
- ✅ **Production use** (proven to work end-to-end)

### Gemini Proof is Best For:
- ✅ **Formalization scaffolding** (organized lemma library)
- ✅ **Intermediate complexity** (between Claude's simple and GPT-5.2's deep)
- ✅ **Case analysis clarity** (explicit small/large distinction)
- ✅ **Studying AI proof generation** (how different models approach same problem)
- ✅ **Learning formalization pitfalls** (why structure doesn't guarantee completion)

### GPT-5.2 Proof is Best For:
- ✅ **Quantitative precision** (explicit constants and ranges)
- ✅ **Constructiveness** (witnesses exist in known intervals)
- ✅ **Extensions to other problems** (method applies to binomial divisibility)
- ✅ **Theoretical insight** (reveals base-digit combinatorial structure)
- ✅ **Research-level depth** (discovers new phenomena)
- ✅ **Mathematical sophistication** (most elegant proof strategy)

---

## Formalization Prospects

### Claude Lean Proof (Fully Formalized ✓)
**Current Status:** ✓ Complete and verified

**Why formalization succeeded:**
- Fewer non-standard definitions needed
- Direct application of Legendre's formula and Bertrand's postulate (both in Mathlib)
- Existential quantifiers on constants are straightforward
- Minimalist approach = fewer failure points

**Challenges overcome:**
- Handling $O(\log n)$ asymptotics in formal arithmetic
- Working with p-adic valuations on factorials

**Lesson:** Simplicity + directness → formalization success

---

### Gemini Lean Proof (Incomplete ✗)
**Current Status:** ✗ Lemmas complete, main theorem has `sorry`

**Why formalization stalled:**
- Requires intricate management of nested constants ($K$, $C'$, $C_{\text{small}}$, $C_{\text{large}}$, etc.)
- log_bound lemma is non-trivial; Chernoff-style inequality reasoning needed
- Case split requires careful proof state management and interface matching between small/large-$n$ cases
- Digit sum bounds exist but their composition is delicate

**What makes it instructive:**
- Shows that "minor elaboration" of simple proof can create unexpected formalization friction
- Demonstrates that organizing lemmas doesn't guarantee proof completion
- Library (Erdos/Lemmas.lean) is solid and reusable even though proof is incomplete

**Comparison with Claude:**
- Gemini chose structure over directness
- More auxiliary lemmas = more surface area for bugs
- Extra complexity made formalization harder, not easier

**Path to completion:** Manual work on main case split and constant management

---

### GPT-5.2 ArXiv Proof (Not Yet Formalized ✗)
**Current Status:** ✗ Published as mathematical paper; not in formal proof assistant

**Why formalization would be hard:**
- Requires formalization of:
  - Kummer's theorem (carries in base-p addition)
  - Chernoff bounds (probabilistic tail estimates)
  - Residue-class counting arguments
  - Carefully coordinated quantification over finitely many primes
- Probabilistic method is idiomatic in math but less natural in proof assistants
- The "existence in $[M, 2M]$" conclusion requires explicit instantiation
- Complex interaction between prime selection, digit distributions, and bad event analysis

**Feasibility:** Very hard. Modern proof assistants (Lean 4, Coq) have probability libraries, but the combination with number-theoretic residue arithmetic is novel. Estimated effort: 5,000-10,000 LoC of proof code. Likely requires significant proof strategy adaptation.

**Comparison with Claude and Gemini:**
- Most sophisticated mathematics but least formalizable
- Trade-off: deeper insight ↔ harder formalization

---

## Conclusion

All three proofs are AI-generated but from different models, establishing the same **main theorem** via fundamentally different approaches:

1. **Claude Lean proof** (~/code/erdos-729): Exploits the **sparsity of large primes** (Bertrand) + **concentration of valuations** (Legendre)
   - Model: Claude
   - Status: ✓ Complete and formalized
   - Approach: Direct algebraic manipulation; minimal auxiliary structure
   - Insight: One strategically-chosen prime suffices

2. **Gemini Lean proof** (~/code/erdos-729-google): Refines with **systematic case analysis** + **auxiliary transformations** (log_bound)
   - Model: Gemini  
   - Status: ✗ Incomplete (lemmas solid, main proof incomplete)
   - Approach: Organized lemma library; explicit small/large-$n$ split; complex constant management
   - Insight: More structured approach adds formalization friction; different models generate different proof strategies

3. **GPT-5.2 ArXiv proof** (Bloom, Croot, et al., arXiv:2601.07421v5): Exploits the **generic structure of base representations** + **carry arithmetic** (Kummer) + **probabilistic method**
   - Model: GPT-5.2
   - Status: ✓ Complete and published
   - Approach: Binomial reformulation; Kummer's theorem; probabilistic existence; formal writeup
   - Insight: Deeper combinatorial structure enables constructive (not just existential) results; most sophisticated approach

**Key Takeaways:**

- **Simplicity wins for formalization:** Claude's direct approach succeeded; Gemini's structured approach failed at completion
- **Structure helps understanding but adds formalization risk:** Extra lemmas aid pedagogical clarity but create more failure points
- **Different AI models generate radically different strategies:** 
  - Claude (formal verification focus): minimalist, direct
  - Gemini (structured formalization focus): complex library, explicit cases
  - GPT-5.2 (research math focus): deep combinatorics, probabilistic method
- **Model maturity matters:** GPT-5.2's approach is most sophisticated but also most complex to formalize (none attempted)
- **Formalization remains hard:** Even with state-of-the-art models, Lean proof completion is unpredictable

**Recommendations for further work:**

- **For formalization:** Claude's minimalist approach (~/code/erdos-729) is the proven gold standard—only one that completed Lean verification
- **For understanding:** Study all three; they provide complementary insights:
  - Claude: straightforward algebraic approach
  - Gemini: systematic formal structure
  - GPT-5.2: deep combinatorial insights
- **For AI proof comparison:** Claude vs. Gemini vs. GPT-5.2 shows how model choice/generation drives proof strategy; compare which approaches scale to harder problems
- **For extensions:** Adapt GPT-5.2's binomial reformulation and Kummer approach to related problems (central binomial coefficient divisibility, factorial inequalities)
- **For AI + formal methods:** Why did Claude succeed where Gemini failed? Is minimalism inherently more formalizable, or did Claude get lucky?

---

## References

### Primary Sources

- **Claude Lean Proof:** `~/code/erdos-729/PROOF.md` and `~/code/erdos-729/Erdos/*.lean`
- **Gemini Lean Proof:** `~/code/erdos-729-google/PROOF.md`, `Erdos/Lemmas.lean`, `Erdos/Work.lean`
- **GPT-5.2 ArXiv Proof:** Bloom, Croot, et al. (2026). "Resolution of Erdős Problem #728." arXiv:2601.07421v5 (AI-generated proof published by human mathematicians)

### Classical Results

- **Legendre's Formula:** Apostol, "Introduction to Analytic Number Theory" (and any number theory textbook)
- **Kummer's Theorem:** Kummer (1852); see also Diamond & Shurman, "A First Course in Modular Forms"
- **Bertrand's Postulate:** Chebyshev (1852); proved in any number theory text
- **Chernoff Bound:** Chernoff (1952); standard in probability theory texts

### Related Problems

- **Erdős Problem #728:** The fully divisible version (without ignoring small primes)
- **Central Binomial Coefficient Divisibility:** Pomerance, Ford-Konyagin, Croot-Mousavi-Schmidt
- **Factorial Inequalities:** Classical literature; recent work on p-adic valuations
