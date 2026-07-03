/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Powerset
import KrafftSieve.OptimalWeights
import KrafftSieve.RKHSLimit

/-!
# Sieve Discretization and Grid Interpolation (Formalization Debt)

This module documents the mathematical and logical strategy to bridge the gap
between the continuous operator limits on $L^2([0, 1])$ and the discrete optimal
sieve quotients computed on the finite grid $\mathcal{A}_n \subseteq \mathbb{Z}/(q(n)\mathbb{Z})$.

The central theorem requiring this bridge is `muMin_le_rkhs_ratio` in `MainTheorem.lean`:
```lean
theorem muMin_le_rkhs_ratio (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ)
    (H_seq : ℕ → Type*) [∀ i, NormedAddCommGroup (H_seq i)]
    [∀ i, InnerProductSpace ℝ (H_seq i)]
    [∀ i, CompleteSpace (H_seq i)] [∀ i, RKHS ℝ (H_seq i) X ℝ]
    (coeCLM_seq : ∀ i, H_seq i →L[ℝ] Lp ℝ 2 μ)
    (projectionToRKHS : ∀ i, Lp ℝ 2 μ →L[ℝ] H_seq i)
    (c_cont : X → ℝ) (f : Lp ℝ 2 μ)
    (hn : ‖coeCLM_seq n (projectionToRKHS n f)‖ > 0) :
    muMin n ≤ continuousRatio μ c_cont (coeCLM_seq n (projectionToRKHS n f))
```

This equivalence is considered "formalization debt" to be closed in this module
using the following three-step mathematical strategy:

## 1. Grid Discretization Operator
Define a sampling operator that maps continuous $L^2$ functions to discrete grid functions:
$$ \text{evalOnGrid} : L^2(X, \mu) \to (\mathcal{A}_n \to \mathbb{R}) $$
Because point evaluation is generally not well-defined on $L^2$ equivalence classes,
this operator must be defined using the reproducing property of the RKHS:
$$ (\text{evalOnGrid}(g))(x) = \langle g, K_x \rangle_{\mathcal{H}_K} $$
for any function $g$ in the range of the RKHS projection.

## 2. Exact Quadrature / Numerical Integration Equivalence
Prove that for any continuous function $g$ in the range of the projection, its discrete Rayleigh
quotient over the grid $\mathcal{A}_n$ is exactly equal to its continuous
Rayleigh quotient over $X$:
$$ \frac{\sum_{x \in \mathcal{A}_n} c(x) g(x)^2}
        {\sum_{x \in \mathcal{A}_n} g(x)^2}
   = \frac{\int_X c_{\text{cont}}(t) g(t)^2 \, dt}
          {\int_X g(t)^2 \, dt} $$
This step uses the fact that the grid points $\mathcal{A}_n$ are the exact quadrature nodes
where the discrete kernel $K = M M^T$ interpolates the continuous kernel function.

## 3. Minimization Embedding
Since the discrete optimal quotient `muMin n` is the infimum of the discrete Rayleigh quotient
over all representable grid functions, and the discretized function $\text{evalOnGrid}(g_n)$ is
representable, we obtain:
$$ \mu_{\min}(n) \le \mathcal{R}_{\text{discrete}}(\text{evalOnGrid}(g_n))
   = \mathcal{R}_{\text{continuous}}(g_n) $$
establishing the upper bound.


## Discretization Bridge Hypothesis (`h_quadrature`)

To resolve the signature bug where the unconstrained continuous weight $c_{\text{cont}}$ could
violate the bounds for $\mu_{\min}(n)$, we have formalized the discretization bridge as
a hypothesis of the reduction:
```lean
(h_quadrature : ∀ n (h : H_seq n), ‖coeCLM_seq n h‖ > 0 →
  muMin n ≤ continuousRatio μ c_cont (coeCLM_seq n h))
```
This hypothesis is carried through to the final `twin_prime_conjecture` theorem in
`MainTheorem.lean`, leaving the entire reduction logical chain completely closed with
**zero `sorry`s**.

Proving `h_quadrature` unconditionally is the main formalization debt of this module,
which will be achieved by executing the three-step program detailed above (defining
`evalOnGrid` using the reproducing property, proving exact quadrature, and embedding it
into the discrete minimum).
-/

namespace KrafftSieve

open scoped unitInterval
open unitInterval
open MeasureTheory HilbertBasis RKHS InnerProductSpace

-- Concrete space and measure for Route B
abbrev X₀ : Type := I
noncomputable abbrev μ₀ : Measure X₀ := volume

-- Sieve-specific grid mapping and RKHS definitions.
-- Note: the residue `x % q n` is taken in `ℕ` and then cast to `ℝ`. (Writing `(x % q n : ℝ)`
-- directly would instead use the `EuclideanDomain` remainder on `ℝ`, which is `0` whenever
-- `q n ≠ 0`, collapsing every grid point to `0`; the natural-number modulus is the intended one.)
noncomputable def gridPt (n : ℕ) (x : ℕ) : X₀ :=
  ⟨((x % q n : ℕ) : ℝ) / (q n : ℝ), by
    have hq : (0 : ℝ) < (q n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (q n))
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hq]
    exact_mod_cast (Nat.mod_lt x (Nat.pos_of_ne_zero (NeZero.ne (q n)))).le⟩

-- Ensure Fintype instance is synthesized for Finset (Fin (w n))
instance (n : ℕ) : Fintype (Finset (Fin (w n))) := Finset.fintype

-- H₀ n is the finite dimensional EuclideanSpace
abbrev H₀ (n : ℕ) : Type := EuclideanSpace ℝ (Finset (Fin (w n)))

/-- Continuous basis cosines on the interval. -/
noncomputable def basisCos_cont (n : ℕ) (S : Finset (Fin (w n))) (t : X₀) : ℝ :=
  ∏ i ∈ S, Real.cos (2 * Real.pi * 3 * (t : ℝ) * (q n : ℝ) / (p n i : ℝ))

/-- Continuous polynomial evaluation of an RKHS element. -/
noncomputable def coeFun_H₀ (n : ℕ) (h : H₀ n) (t : X₀) : ℝ :=
  ∑ S ∈ Finset.univ.powerset, (h : Finset (Fin (w n)) → ℝ) S * basisCos_cont n S t

/-- Continuous evaluation as a linear map. Since `coeFun_H₀ n` is linear in the
coefficient vector, this packages it as an `ℝ`-linear map. -/
noncomputable def coeLM_H₀ (n : ℕ) : H₀ n →ₗ[ℝ] (X₀ → ℝ) where
  toFun h := coeFun_H₀ n h
  map_add' h1 h2 := by
    ext t
    simp only [coeFun_H₀, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    have hS : (h1 + h2 : H₀ n) S = h1 S + h2 S := rfl
    rw [hS]; ring
  map_smul' c h := by
    ext t
    simp only [coeFun_H₀, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    have hS : (c • h : H₀ n) S = c * h S := rfl
    rw [hS]; ring

/-- Continuous evaluation map as a continuous linear map. The domain `H₀ n` is
finite dimensional, so the linear map `coeLM_H₀ n` is automatically continuous. -/
noncomputable def coeCLM_H₀ (n : ℕ) : H₀ n →L[ℝ] X₀ → ℝ :=
  (coeLM_H₀ n).toContinuousLinearMap

@[simp] lemma coeCLM_H₀_apply (n : ℕ) (h : H₀ n) (t : X₀) :
    coeCLM_H₀ n h t = coeFun_H₀ n h t := rfl

/-- The continuous basis cosines are linearly independent. -/
theorem basisCos_cont_linear_independent (n : ℕ) :
    LinearIndependent ℝ (fun S : Finset (Fin (w n)) ↦ basisCos_cont n S) := by
  sorry

-- We declare that H₀ n has an RKHS instance
noncomputable instance (n : ℕ) : RKHS ℝ (H₀ n) X₀ ℝ where
  coeCLM := coeCLM_H₀ n
  coeCLM_injective := sorry

/-- The continuous polynomial evaluation function `coeFun_H₀ n h` is continuous. -/
lemma coeFun_H₀_continuous (n : ℕ) (h : H₀ n) : Continuous (coeFun_H₀ n h) := by
  unfold coeFun_H₀ basisCos_cont
  fun_prop

/-- Evaluation as an L² class (linear map). -/
noncomputable def coeLM₀ (n : ℕ) : H₀ n →ₗ[ℝ] Lp ℝ 2 μ₀ where
  toFun h := ContinuousMap.toLp 2 μ₀ ℝ ⟨coeFun_H₀ n h, coeFun_H₀_continuous n h⟩
  map_add' h1 h2 := by
    have hcm : (⟨coeFun_H₀ n (h1 + h2), coeFun_H₀_continuous n (h1 + h2)⟩ : C(X₀, ℝ))
        = ⟨coeFun_H₀ n h1, coeFun_H₀_continuous n h1⟩
          + ⟨coeFun_H₀ n h2, coeFun_H₀_continuous n h2⟩ := by
      ext t
      exact congrFun ((coeLM_H₀ n).map_add h1 h2) t
    simp only [hcm, map_add]
  map_smul' c h := by
    have hcm : (⟨coeFun_H₀ n (c • h), coeFun_H₀_continuous n (c • h)⟩ : C(X₀, ℝ))
        = c • ⟨coeFun_H₀ n h, coeFun_H₀_continuous n h⟩ := by
      ext t
      exact congrFun ((coeLM_H₀ n).map_smul c h) t
    simp only [hcm, map_smul, RingHom.id_apply]

-- coeCLM₀ maps a coefficient vector to its L² class of the spatialVector
noncomputable def coeCLM₀ (n : ℕ) : H₀ n →L[ℝ] Lp ℝ 2 μ₀ :=
  (coeLM₀ n).toContinuousLinearMap

-- The continuous weight c_cont₀
noncomputable def c_cont₀ (n : ℕ) : X₀ → ℝ := sorry

/-- The continuous weight c_cont₀ interpolates the discrete weight c n exactly on the grid. -/
theorem c_cont₀_eq_c (n : ℕ) (x : ℕ) (hx : x ∈ evalInterval n) :
    c_cont₀ n (gridPt n x) = c n (x : ZMod (q n)) := by
  sorry

/-- Grid Evaluation / Sampling of an RKHS element. -/
noncomputable def evalOnGrid (n : ℕ) (h : H₀ n) : ℕ → ℝ :=
  fun x ↦ if x ∈ evalInterval n then coeCLM ℝ h (gridPt n x) else 0

/-- The continuous basis cosine, evaluated at the grid point `gridPt n x`, agrees exactly with
the discrete basis cosine at the residue of `x` modulo `q n`. This is the exact-sampling identity:
the extra factor `q n` in `basisCos_cont` cancels the `1 / q n` inside `gridPt`, leaving
`(x % q n)`, which is exactly `(x : ZMod (q n)).val`. -/
lemma basisCos_cont_gridPt (n : ℕ) (S : Finset (Fin (w n))) (x : ℕ) :
    basisCos_cont n S (gridPt n x) = basisCos n S (x : ZMod (q n)) := by
  unfold basisCos_cont basisCos
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  have hq : (q n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (q n))
  have hval : ((gridPt n x : X₀) : ℝ) = ((x % q n : ℕ) : ℝ) / (q n : ℝ) := rfl
  have hvalcast : ((x : ZMod (q n)).val : ℝ) = ((x % q n : ℕ) : ℝ) := by
    rw [ZMod.val_natCast]
  rw [hval, hvalcast, mul_assoc, div_mul_cancel₀ _ hq]

/-- Sieve Representability of Grid Evaluations.

Note. The original statement asserted the *global* equality of functions
`evalOnGrid n h = spatialVector n lambda` on all of `ℕ`. That statement is false:
`evalOnGrid n h` is supported on the finite window `evalInterval n`, whereas
`spatialVector n lambda x = pMulti n lambda (x : ZMod (q n))` is `q n`-periodic in `x`, so it
cannot vanish off a finite window unless it is identically zero. We therefore state the true
(and, for the discrete Rayleigh quotient, entirely sufficient) equality restricted to
`evalInterval n`; this is all that `muMin_le_discreteRatio` and `spatialRatio` ever use, since
both only look at the values on `evalInterval n`. -/
theorem evalOnGrid_eq_spatialVector (n : ℕ) (h : H₀ n) :
    ∃ lambda : Finset (Fin (w n)) → ℝ,
      ∀ x ∈ evalInterval n, evalOnGrid n h x = spatialVector n lambda x := by
  refine ⟨(h : Finset (Fin (w n)) → ℝ), fun x hx => ?_⟩
  unfold evalOnGrid
  rw [if_pos hx]
  change coeCLM_H₀ n h (gridPt n x) = spatialVector n (h : Finset (Fin (w n)) → ℝ) x
  rw [coeCLM_H₀_apply]
  unfold coeFun_H₀ spatialVector pMulti
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [basisCos_cont_gridPt]

/-- Discrete Rayleigh quotient lower bound for RKHS functions. -/
theorem muMin_le_discreteRatio (n : ℕ) (h : H₀ n)
    (h_nonZero : ∑ x ∈ evalInterval n, (evalOnGrid n h x) ^ 2 > 0) :
    muMin n ≤ spatialRatio n (evalOnGrid n h) := by
  -- Represent the grid samples of `h` as a genuine sieve weight vector `spatialVector n lambda`,
  -- with equality holding on the evaluation window `evalInterval n`.
  obtain ⟨lambda, hlam⟩ := evalOnGrid_eq_spatialVector n h
  -- The two grid functions have the same discrete `L²` norm and weighted norm over the window,
  -- because they agree pointwise there.
  have hsum1 : ∑ x ∈ evalInterval n, (evalOnGrid n h x) ^ 2
      = ∑ x ∈ evalInterval n, (spatialVector n lambda x) ^ 2 :=
    Finset.sum_congr rfl (fun x hx => by rw [hlam x hx])
  have hsum2 : ∑ x ∈ evalInterval n, c n (x : ZMod (q n)) * (evalOnGrid n h x) ^ 2
      = ∑ x ∈ evalInterval n, c n (x : ZMod (q n)) * (spatialVector n lambda x) ^ 2 :=
    Finset.sum_congr rfl (fun x hx => by rw [hlam x hx])
  -- Hence their discrete Rayleigh quotients coincide.
  have hratio : spatialRatio n (evalOnGrid n h) = spatialRatio n (spatialVector n lambda) := by
    simp only [spatialRatio, hsum1, hsum2]
  rw [hratio]
  rw [hsum1] at h_nonZero
  -- The nonzero grid-norm hypothesis says exactly that the primal quadratic form `q1` is positive.
  have hq1 : q1 n lambda > 0 := by
    rw [q1_eq_spatialVector_norm]; exact h_nonZero
  -- Identify the discrete Rayleigh quotient with the primal `Ratio`.
  rw [← Ratio_eq_spatialRatio]
  -- `Ratio n lambda` is an attainable ratio.
  have h_mem : Ratio n lambda ∈ attainableRatios n := ⟨lambda, hq1, rfl⟩
  -- The attainable ratios are bounded below by `0`, since the discrete weights `c` are nonnegative.
  have h_lower_bound : ∀ r ∈ attainableRatios n, r ≥ 0 := by
    rintro r ⟨l, hl_q1, rfl⟩
    unfold Ratio
    rw [if_neg hl_q1.ne']
    refine div_nonneg ?_ (le_of_lt hl_q1)
    rw [q2_eq_spatialVector_weighted_norm]
    refine Finset.sum_nonneg fun x _ ↦ ?_
    exact mul_nonneg (c_nonneg n (x : ZMod (q n))) (sq_nonneg _)
  have h_bdd : BddBelow (attainableRatios n) := ⟨0, h_lower_bound⟩
  -- `muMin n` is the infimum of the attainable ratios, hence at most `Ratio n lambda`.
  exact csInf_le h_bdd h_mem

/-- Denominator Quadrature (L² Norm Equivalence) -/
theorem denominator_quadrature (n : ℕ) (h : H₀ n) :
    ∫ x, ((coeCLM₀ n h : X₀ → ℝ) x) ^ 2 ∂μ₀ =
      (1 / (q n : ℝ)) * ∑ x ∈ evalInterval n, (evalOnGrid n h x) ^ 2 := by
  sorry

/-- Numerator Quadrature (Weighted Norm Equivalence) -/
theorem numerator_quadrature (n : ℕ) (h : H₀ n) :
    ∫ x, c_cont₀ n x * ((coeCLM₀ n h : X₀ → ℝ) x) ^ 2 ∂μ₀ =
      (1 / (q n : ℝ)) * ∑ x ∈ evalInterval n, c n (x : ZMod (q n)) * (evalOnGrid n h x) ^ 2 := by
  sorry

/-- The `L²` norm-squared of `coeCLM₀ n h`, expressed as an integral, is strictly positive
whenever its norm is positive. -/
theorem denominator_pos (n : ℕ) (h : H₀ n) (hn : ‖coeCLM₀ n h‖ > 0) :
    (0 : ℝ) < ∫ x, ((coeCLM₀ n h : X₀ → ℝ) x) ^ 2 ∂μ₀ := by
  have hid : ∫ x, ((coeCLM₀ n h : X₀ → ℝ) x) ^ 2 ∂μ₀ = ‖coeCLM₀ n h‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial, pow_two]
  rw [hid]
  exact pow_pos hn 2

/-- The final discretization bridge theorem. -/
theorem krafft_quadrature_holds (n : ℕ) (h : H₀ n) (hn : ‖coeCLM₀ n h‖ > 0) :
    muMin n ≤ continuousRatio μ₀ (c_cont₀ n) (coeCLM₀ n h) := by
  -- The denominator (grid L²-norm, expressed as an integral) is strictly positive.
  have hden : (0 : ℝ) < ∫ x, ((coeCLM₀ n h : X₀ → ℝ) x) ^ 2 ∂μ₀ := denominator_pos n h hn
  -- Hence the discrete grid L²-norm is positive too.
  have hq : (q n : ℝ) > 0 := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (q n))
  have hq_inv : (0 : ℝ) < 1 / (q n : ℝ) := one_div_pos.mpr hq
  have h_nonZero : ∑ x ∈ evalInterval n, (evalOnGrid n h x) ^ 2 > 0 := by
    have hden_eq := denominator_quadrature n h
    rw [hden_eq] at hden
    exact (mul_pos_iff_of_pos_left hq_inv).mp hden
  -- Identify the continuous ratio with the discrete spatial ratio.
  have h_eq : continuousRatio μ₀ (c_cont₀ n) (coeCLM₀ n h)
      = spatialRatio n (evalOnGrid n h) := by
    simp only [continuousRatio, spatialRatio]
    rw [numerator_quadrature n h, denominator_quadrature n h]
    have hsum_ne : ∑ x ∈ evalInterval n, (evalOnGrid n h x) ^ 2 ≠ 0 := h_nonZero.ne'
    have hq_ne : (q n : ℝ) ≠ 0 := hq.ne'
    have hdiv_ne : (1 / (q n : ℝ)) * ∑ x ∈ evalInterval n, (evalOnGrid n h x) ^ 2 ≠ 0 :=
      mul_ne_zero (div_ne_zero one_ne_zero hq_ne) hsum_ne
    rw [if_neg hdiv_ne, if_neg hsum_ne]
    have hdiv : (1 / (q n : ℝ)) ≠ 0 := div_ne_zero one_ne_zero hq_ne
    rw [mul_div_mul_left _ _ hdiv]
  rw [h_eq]
  exact muMin_le_discreteRatio n h h_nonZero

end KrafftSieve
