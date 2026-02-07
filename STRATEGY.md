# Proof Strategy for Erdős Factorial Divisibility Conjecture

## Problem Statement

Prove that if $ a! b! \mid n! $ "ignoring what happens on small primes", then $ a + b \leq n + O(\log n) $.

This extends the classical Erdős result (which holds for full divisibility) to the case where we only require divisibility for primes above some threshold $ P $.

## Overall Approach

We follow the Barreto-Leeham approach, which extends Erdős's original proof technique using Legendre's formula for p-adic valuations.

### Key Insight

The original Erdős proof uses powers of 2 alone. For any prime $ p $, Legendre's formula gives:

$$ v_p(n!) = \sum_{i \geq 1} \left\lfloor \frac{n}{p^i} \right\rfloor = \frac{n}{p-1} + O(\log_p n) $$

If $ a! b! \mid n! $, then $ v_p(a!) + v_p(b!) \leq v_p(n!) $ for all primes $ p $.

Using Legendre's formula:
$$ \frac{a}{p-1} + \frac{b}{p-1} + O(\log n) \leq \frac{n}{p-1} + O(\log n) $$

Simplifying:
$$ \frac{a + b}{p-1} \leq \frac{n}{p-1} + O(\log n) $$

Taking $ p \to \infty $ (considering only large primes), we get $ a + b \leq n + O(\log n) $.

### Why "Ignoring Small Primes" Doesn't Change the Result

The key observation is that the asymptotic bound $ a + b \leq n + O(\log n) $ comes from analyzing large primes. Small primes ($ p \leq P $) can only contribute a bounded amount to the factorization, which gets absorbed into the $ O(\log n) $ term.

## Proof Decomposition (Task DAG)

### Phase 1: Natural Language Proof
**Task**: erdos-csg  
**Role**: execute  
**Output**: PROOF.md

Write a complete, rigorous natural language proof that:
1. Defines "ignoring small primes" precisely
2. Uses Legendre's formula
3. Shows how large primes dominate the bound
4. Explains why small primes don't affect the asymptotic bound

### Phase 2: Formalize Theorem Statement
**Task**: erdos-d2f  
**Role**: execute  
**Output**: Erdos/Basic.lean (theorem statement with sorry)

Create the formal Lean 4 statement:
- Import necessary Mathlib modules (Factorial, Prime, PadicVal, Asymptotics)
- Define "ignoring small primes" formally
- State main theorem with exact correspondence to PROBLEM.md
- Use sorry for proof body (filled in later phases)

### Phase 3: Verify Statement
**Task**: erdos-vxn  
**Role**: verify  
**Dependencies**: erdos-d2f

Verify that:
1. Lean statement matches PROBLEM.md exactly
2. No additional assumptions added
3. Code compiles with `lake build`
4. Statement is ready for proof implementation

### Phase 4: Prove Supporting Lemmas

#### Phase 4.1: Legendre Formula Lemma
**Task**: erdos-lnq  
**Role**: execute  
**Dependencies**: erdos-vxn  
**Verification**: erdos-vs2

Prove: $ v_p(n!) = \sum_{i \geq 1} \lfloor n/p^i \rfloor = n/(p-1) + O(\log n) $

Use or extend Mathlib's p-adic valuation results.

#### Phase 4.2: Large Primes Domination Lemma
**Task**: erdos-lgm  
**Role**: execute  
**Dependencies**: erdos-vxn  
**Verification**: erdos-typ

Prove: For $ p > P $, if $ v_p(a!) + v_p(b!) \leq v_p(n!) $, then taking $ p \to \infty $ gives $ a + b \leq n + O(\log n) $.

This uses the Legendre formula from Phase 4.1.

### Phase 5: Assemble Final Proof
**Task**: erdos-89x  
**Role**: execute  
**Dependencies**: erdos-vs2, erdos-typ (both lemmas verified)

Combine the proven lemmas to complete the main theorem proof:
1. Assume $ a! b! \mid n! $ for all primes $ p > P $
2. Apply p-adic valuations: $ v_p(a!) + v_p(b!) \leq v_p(n!) $ for $ p > P $
3. Use Legendre formula (Phase 4.1)
4. Use large primes argument (Phase 4.2)
5. Conclude $ a + b \leq n + O(\log n) $

Remove all sorry statements.

### Phase 6: Final Verification
**Task**: erdos-10y  
**Role**: verify  
**Dependencies**: erdos-89x  
**Priority**: 0 (Critical)

Verify all three success criteria from PROBLEM.md:
1. ✓ Main theorem statement corresponds to problem (no extra assumptions)
2. ✓ Lean theorem compiles with `lake build`
3. ✓ No sorry in codebase (check with grep)

Also verify PROOF.md exists and matches the Lean proof.

## Dependency Graph

```
erdos-csg (Phase 1: Natural language proof)
    ↓ (parallel with Phase 2-6)
erdos-d2f (Phase 2: Formalize statement)
    ↓
erdos-vxn (Phase 3: Verify statement)
    ↓
    ├─→ erdos-lnq (Phase 4.1: Legendre lemma)
    │       ↓
    │   erdos-vs2 (Verify 4.1)
    │       ↓
    │       └───→ erdos-89x (Phase 5: Final assembly)
    │                 ↓
    └─→ erdos-lgm (Phase 4.2: Large primes lemma)
            ↓
        erdos-typ (Verify 4.2)
            ↓
            └───→ erdos-89x
                      ↓
                  erdos-10y (Phase 6: Final verification)
```

## Critical Constraints

### Immutable Definitions
- Executors MUST NOT modify the theorem statement from PROBLEM.md
- If the problem as stated is unprovable, ESCALATE to advisor
- Do not add convenient assumptions

### Compilation Requirement
- ALL Lean tasks must include `--test "lake build"`
- Code must compile at every stage

### No Sorry Policy
- Lemmas in Phase 4 must be proven (no sorry)
- Final proof in Phase 5 must have no sorry
- Phase 6 verification checks this with grep

## Success Criteria

The project succeeds when Phase 6 verification confirms:
1. The Lean statement exactly matches the natural language problem
2. `lake build` succeeds
3. No sorry in Erdos/ directory (only our code, not upstream Mathlib)

## Current Status

- ✓ Task DAG created
- ○ Phase 1 ready to start (erdos-csg)
- ○ Phase 2 ready to start (erdos-d2f)
- Waiting: Phase 3-6 (blocked on dependencies)

Execute and verify agents can now proceed with the unblocked tasks.
