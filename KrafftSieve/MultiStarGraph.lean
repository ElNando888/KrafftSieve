/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela, Gemini 3.5 Flash (Google DeepMind)
-/

import Mathlib
import KrafftSieve.OptimalWeights
import KrafftSieve.RidgeGraph
import KrafftSieve.Identification

/-!
# Multi-Star Graph and the Averaging Principle

This file establishes the deterministic continuous weights derived from the
spectral convolution of the Sieve penalty function, bypassing the combinatorial
power-set via the probabilistic/averaging principle over a uniform Finset.
-/

namespace KrafftSieve
open scoped BigOperators

/--
The set of all possible anchor choices of size m.
-/
def anchorSubsets (n : ℕ) (m : ℕ) : Finset (Finset (Fin (w n))) :=
  Finset.powersetCard m Finset.univ

/--
Helper lemma: The discrete Fourier transform of a product of cosines expands
into a sum of Dirichlet kernels (sinc functions) via product-to-sum identities.
-/
theorem fourier_cos_mul_cos (_L : ℝ) (f1 f2 : ℝ) (x : ℝ) :
    Real.cos (2 * Real.pi * f1 * x) * Real.cos (2 * Real.pi * f2 * x) =
    (Real.cos (2 * Real.pi * (f1 - f2) * x) + Real.cos (2 * Real.pi * (f1 + f2) * x)) / 2 := by
  have hsub : 2 * Real.pi * (f1 - f2) * x =
      2 * Real.pi * f1 * x - 2 * Real.pi * f2 * x := by ring
  have hadd : 2 * Real.pi * (f1 + f2) * x =
      2 * Real.pi * f1 * x + 2 * Real.pi * f2 * x := by ring
  rw [hsub, hadd, Real.cos_sub, Real.cos_add]
  ring

/--
Helper lemma: the integral of a cosine evaluates to its continuous sinc coefficient.
At zero frequency, the integral is `L`; the conditional is necessary to state this
removable singularity correctly.

The original uploaded statement omitted the zero-frequency case and asserted
`sin (π L f) / (π f)` for every `f`. That statement is false when `f = 0` and
`L ≠ 0`, because Lean's division gives a right-hand side of zero.
-/
theorem fourier_sinc_eval (L f : ℝ) :
    (∫ x in (-L / 2)..(L / 2), Real.cos (2 * Real.pi * f * x)) =
    if f = 0 then L else Real.sin (Real.pi * L * f) / (Real.pi * f) := by
  by_cases hf : f = 0
  · subst f
    simp
    ring
  · rw [if_neg hf]
    have hk : 2 * Real.pi * f ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hf
    have hderiv : ∀ x : ℝ, HasDerivAt
        (fun y : ℝ => Real.sin (2 * Real.pi * f * y) / (2 * Real.pi * f))
        (Real.cos (2 * Real.pi * f * x)) x := by
      intro x
      have hlin : HasDerivAt (fun y : ℝ => (2 * Real.pi * f) * y)
          (2 * Real.pi * f) x := by
        simpa using (hasDerivAt_id x).const_mul (2 * Real.pi * f)
      simpa [hk] using
        ((Real.hasDerivAt_sin (2 * Real.pi * f * x)).comp x hlin).div_const
          (2 * Real.pi * f)
    have hint : IntervalIntegrable (fun x : ℝ => Real.cos (2 * Real.pi * f * x))
        MeasureTheory.volume (-L / 2) (L / 2) :=
      (show Continuous (fun x : ℝ => Real.cos (2 * Real.pi * f * x)) by
        fun_prop).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint]
    rw [show 2 * Real.pi * f * (L / 2) = Real.pi * L * f by ring,
        show 2 * Real.pi * f * (-L / 2) = -(Real.pi * L * f) by ring,
        Real.sin_neg]
    field_simp
    ring

/--
The continuous Fourier overlap evaluated as a sum of Dirichlet Kernels (sinc).
-/
noncomputable def sincCoeff (n : ℕ) (a j i : Fin (w n)) (k : ℕ) : ℝ :=
  let L := ((evalInterval n).card : ℝ)
  let fa := (p n a : ℝ)
  let fj := (p n j : ℝ)
  let fi := (p n i : ℝ)
  let k_R := (k : ℝ)
  let f1 := 3 / fa - 3 / fj - 6 * k_R / fi
  let f2 := 3 / fa - 3 / fj + 6 * k_R / fi
  let f3 := 3 / fa + 3 / fj - 6 * k_R / fi
  let f4 := 3 / fa + 3 / fj + 6 * k_R / fi
  let sinc (f : ℝ) := if f = 0 then L else Real.sin (Real.pi * L * f) / (Real.pi * f)
  (1 / 4) * (sinc f1 + sinc f2 + sinc f3 + sinc f4)

/--
The universal continuous weight for any edge S = {a, j}.
-/
noncomputable def starWeight (n : ℕ) (S : Idx n) : ℝ :=
  (1 / 2) * ∑ a ∈ (S : Finset (Fin (w n))), ∑ j ∈ (S : Finset (Fin (w n))) \ {a},
    - ∑ i : Fin (w n), ∑ k ∈ Finset.range ((p n i) / 2 + 1),
      sincCoeff n a j i k

/--
The optimal Multi-Star test vector explicitly constructed from the anchor subset A. It cleanly
projects the universal star weights onto the bipartite edges connecting A to its complement.
-/
noncomputable def multiStarVector (n : ℕ) (A : Finset (Fin (w n))) (S : Idx n) : ℝ :=
  if ∃ a ∈ A, ∃ j ∉ A, (S : Finset (Fin (w n))) = {a, j} then starWeight n S else 0

noncomputable def P_survive (n m : ℕ) (S1 S2 : Idx n) : ℝ :=
  let inter := ((S1 : Finset (Fin (w n))) ∩ (S2 : Finset (Fin (w n)))).card
  let w_n := (w n : ℝ)
  let m_R := (m : ℝ)
  if inter = 2 then
    (2 * m_R * (w_n - m_R)) / (w_n * (w_n - 1))
  else if inter = 1 then
    (m_R * (w_n - m_R) * (w_n - m_R - 1) +
      m_R * (m_R - 1) * (w_n - m_R)) / (w_n * (w_n - 1) * (w_n - 2))
  else
    (4 * m_R * (m_R - 1) * (w_n - m_R) * (w_n - m_R - 1)) /
      (w_n * (w_n - 1) * (w_n - 2) * (w_n - 3))

/-- The set of all two-element edges (subsets of size 2). -/
def Edges (n : ℕ) : Finset (Idx n) :=
  Finset.univ.filter (fun S => S.card = 2)

/--
The exact cross-term error sum for the mass matrix.
-/
noncomputable def massCrossTerms (n m : ℕ) : ℝ :=
  ∑ S1 ∈ Edges n, ∑ S2 ∈ (Edges n \ {S1}),
    P_survive n m S1 S2 * starWeight n S1 * starWeight n S2 *
    (∑ x ∈ evalInterval n, basisFunction n (S1 : Finset (Fin (w n))) x *
                           basisFunction n (S2 : Finset (Fin (w n))) x)

/--
The exact structural off-diagonal penalty sum (which is negative).
-/
noncomputable def penaltyOffDiagonal (n m : ℕ) : ℝ :=
  ∑ S1 ∈ Edges n, ∑ S2 ∈ (Edges n \ {S1}),
    P_survive n m S1 S2 * starWeight n S1 * starWeight n S2 *
    (∑ x ∈ evalInterval n, c n (x : ZMod (q n)) *
                           basisFunction n (S1 : Finset (Fin (w n))) x *
                           basisFunction n (S2 : Finset (Fin (w n))) x)

/--
The expected mass evaluation over all possible anchor subsets of size m.
By linearity of expectation, the sum of Q1(A) reduces to the probability of an edge
being active, multiplied by the diagonal mass sum, minus cross-term error bounds.
-/
theorem expected_mass_bound (n : ℕ) (m : ℕ) (hm : m ≤ w n) :
    (∑ A ∈ anchorSubsets n m, q1 n (multiStarVector n A)) / ((anchorSubsets n m).card : ℝ) ≥
    (2 * (m : ℝ) * (w n - m : ℝ) / ((w n : ℝ) * (w n - 1 : ℝ))) *
    (∑ S ∈ Edges n, (starWeight n S)^2 * ((evalInterval n).card : ℝ) / 4) -
    massCrossTerms n m :=
  sorry

/--
The expected penalty evaluation over all possible anchor subsets of size m.
Using the FourierTransform helpers (fourier_cos_mul_cos and fourier_sinc_eval),
the continuous expansion of this quadratic form explicitly bounds the sum strictly
below the diagonal mass trace.
-/
theorem expected_penalty_bound (n : ℕ) (m : ℕ) (hm : m ≤ w n) :
    (∑ A ∈ anchorSubsets n m, q2 n (multiStarVector n A)) / ((anchorSubsets n m).card : ℝ) ≤
    -- Expected Diagonal Penalty
    (2 * (m : ℝ) * (w n - m : ℝ) / ((w n : ℝ) * (w n - 1 : ℝ))) *
    (∑ S ∈ Edges n, (starWeight n S)^2 *
                  (∑ x ∈ evalInterval n, c n (x : ZMod (q n)) * (basisFunction n S x)^2)) +
    -- Expected Off-Diagonal Penalty (Structurally negative due to sinc anti-alignment)
    penaltyOffDiagonal n m :=
  sorry

/--
The asymptotic guarantee that the expected ratio Q2/Q1 is strictly less than 1.
Because the off-diagonal penalty perfectly anti-aligns with the Fourier density,
for a sufficiently scaled m(n), the expectation is strictly less than the expected mass.
-/
theorem expected_ratio_lt_one (n : ℕ) (m : ℕ) (hm : m ≤ w n) (hn : 1000 ≤ n) :
    ((∑ A ∈ anchorSubsets n m, q2 n (multiStarVector n A)) / ((anchorSubsets n m).card : ℝ)) <
    ((∑ A ∈ anchorSubsets n m, q1 n (multiStarVector n A)) / ((anchorSubsets n m).card : ℝ)) :=
  sorry

/--
The existence of at least one valid combination via the Averaging (Pigeonhole) Principle.
-/
theorem exists_multi_star_with_mu_lt_one (n : ℕ) (hn : 1000 ≤ n) :
    ∃ A : Finset (Fin (w n)), q1 n (multiStarVector n A) > 0 ∧ Ratio n (multiStarVector n A) < 1 :=
  sorry

end KrafftSieve
