# Roadmap for the remaining `RidgeGraph` bounds

This blueprint concerns the two remaining `sorry`s in
`KrafftSieve/RidgeGraph.lean`.

## 1. `testPenalty_upper_bound`

### First checkpoint: validate or repair the statement

The present clique hypothesis controls only `massMatrixEntry`; it contains no
condition on `penaltyMatrixEntry` or on the hit counter `c`.  Consequently the
claimed penalty estimate does **not** follow directly from the definition of a
ridge.

A particularly important test case is the singleton clique `C = {∅}`.  It is a
clique vacuously, and the desired inequality reduces to

```text
∑ x ∈ evalInterval n, c n x ≤ (evalInterval n).card.
```

An exploratory finite calculation at `n = 2` gives a candidate obstruction:
the interval has 28 elements while the total hit count appears to be 29.  This
calculation is not yet a Lean proof, so the first formal task should be to
encode and kernel-check this finite case.  If confirmed, the theorem is false
as stated and should be replaced rather than attacked with tactics.

### Recommended repaired interface

Prove the analytic/destructive-interference estimate separately and expose it
as an explicit hypothesis or a strengthened graph invariant.  Two reasonable
forms are:

```lean
(h_penalty : ∀ S ∈ C, ∀ T ∈ C,
  penaltyMatrixEntry n S T ≤ if S = T then (evalInterval n).card else 0)
```

or, more directly,

```lean
(h_penalty : testPenalty n C ≤ (C.card : ℝ) * (evalInterval n).card)
```

The first form retains mathematical content in `testPenalty_upper_bound`.
Its proof then splits the double sum into diagonal and off-diagonal terms:

1. Prove a diagonal estimate for every `S ∈ C`.
2. Prove nonpositivity (or a sufficiently strong aggregate cancellation bound)
   for off-diagonal entries.
3. Split each inner sum at `{S}`, sum the two estimates, and rewrite
   `∑ _ ∈ C, (evalInterval n).card` as
   `(C.card : ℝ) * (evalInterval n).card`.

The real mathematical work is therefore not finite-sum bookkeeping but a new
lemma connecting `c`, the cosine basis, and phase-locking.  The existing exact
Dirichlet expansion only treats `massMatrixEntry`; a parallel expansion for
`penaltyMatrixEntry` is likely needed.  Suggested decomposition:

- expand `c` as `∑ i, g n i x` and commute finite sums;
- establish a Fourier/cosine expansion for each residue indicator `g n i`;
- combine it with `dirichlet_prod_cos_expand`;
- prove the required sign or aggregate cancellation estimate;
- package that estimate as the off-diagonal lemma above.

Do not attempt to derive destructive interference merely from
`massMatrixEntry > ridgeThreshold`: that implication is absent from the
current definitions.

## 2. `rayleigh_quotient_bound`

Once a valid penalty estimate is available, strengthen the mass theorem with a
strict companion:

```lean
testMass n C >
  (C.card : ℝ) * ((C.card : ℝ) - 1) * ridgeThreshold n
```

under `h_clique` and `2 ≤ C.card`.  This follows by preserving the strict
inequality for at least one off-diagonal term instead of weakening every ridge
entry from `>` to `≥`.  Since

```lean
ridgeThreshold n = (evalInterval n).card / 2,
```

and `h_large : (C.card : ℝ) > 2` implies the natural-number fact
`3 ≤ C.card`, one gets

```text
(C.card) * (C.card - 1) * card(evalInterval) / 2
  ≥ (C.card) * card(evalInterval).
```

Combining this with the strict mass bound and the repaired penalty upper bound
produces

```text
testPenalty n C < testMass n C.
```

The final division step must explicitly establish `0 < testMass n C`, then use
an ordered-field division lemma (or `div_lt_one` after rewriting) to conclude
`testPenalty n C / testMass n C < 1`.

### Why the existing weak mass theorem alone is insufficient

For `C.card = 3`, `testMass_lower_bound` gives only

```text
testMass n C ≥ 3 * (evalInterval n).card,
```

while `testPenalty_upper_bound` gives `testPenalty n C ≤` the same quantity.
Those non-strict inequalities imply a quotient at most one, not strictly less
than one.  The strict companion is therefore necessary unless the penalty
bound itself is strengthened to a strict inequality.

## Suggested proof order

1. Kernel-check the `n = 2`, `C = {∅}` candidate counterexample.
2. If confirmed, correct `testPenalty_upper_bound` by adding the genuinely
   needed cancellation assumption or strengthening the ridge structure.
3. Formalize the diagonal penalty lemma.
4. Formalize the off-diagonal/aggregate destructive-interference lemma via a
   penalty Dirichlet expansion.
5. Assemble the corrected penalty upper bound.
6. Prove the strict mass companion while reusing the now-complete
   `testMass_lower_bound` bookkeeping.
7. Derive positivity of `testMass` and close the quotient inequality.
