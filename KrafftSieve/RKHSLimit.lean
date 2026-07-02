/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import KrafftSieve.RKHSLimitAux

/-!
# RKHS Limits and Mercer's Theorem

This file formalizes the Reproducing Kernel Hilbert Space (RKHS) projection limit
sequence as $n \to \infty$ and states Mercer's spectral theorem for vector-valued RKHS.
-/

open MeasureTheory Matrix HilbertBasis RKHS InnerProductSpace Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X V]
variable (μ : Measure X) [IsFiniteMeasure μ]

-- The continuity assumption wrapped as a Fact
variable [hK : Fact (Continuous (fun (p : X × X) ↦ kernel H p.1 p.2))]

-- The integral operator as a continuous linear map from L^2 to L^2
def integralOperator : Lp V 2 μ →L[𝕜] Lp V 2 μ := sorry

/--
The continuous Rayleigh quotient of a function in L^2.
-/
noncomputable def continuousRatio (c_cont : X → ℝ) (f : Lp ℝ 2 μ) : ℝ :=
  let num := ∫ x, c_cont x * (f : X → ℝ) x ^ 2 ∂μ
  let den := ∫ x, (f : X → ℝ) x ^ 2 ∂μ
  if den = 0 then 0 else num / den

/--
Theorem: There exists a continuous test function in L^2 whose continuous
Rayleigh quotient is strictly less than 1.
-/
theorem exists_continuous_ratio_lt_one (c_cont : X → ℝ)
    (h_dip : ∃ s : Set X, MeasurableSet s ∧ 0 < μ s ∧ ∀ x ∈ s, c_cont x < 1) :
    ∃ f : Lp ℝ 2 μ, ‖f‖ > 0 ∧ continuousRatio μ c_cont f < 1 := by
  sorry

/--
The continuous bilinear form associated with the weighted L^2 inner product.
-/
noncomputable def weightedBilinearForm (c : X → ℝ) [Fact (Continuous c)] :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (weightedBilinearFormLin μ c)
    (weightedBilinearForm_exists_bound μ c).choose
    (weightedBilinearForm_exists_bound μ c).choose_spec

omit [IsFiniteMeasure μ] in
theorem weightedBilinearForm_apply (c : X → ℝ) [Fact (Continuous c)] (g h : Lp ℝ 2 μ) :
    weightedBilinearForm μ c g h = ∫ x, c x * (g : X → ℝ) x * (h : X → ℝ) x ∂μ := by
  simp only [weightedBilinearForm, LinearMap.mkContinuous₂_apply, weightedBilinearFormLin_apply]

/-
Theorem: The quadratic form `g ↦ ∫ x, c x * g(x)^2` is continuous on L^2.
-/
omit [IsFiniteMeasure μ] in
theorem quadratic_form_continuous (c : X → ℝ) [Fact (Continuous c)] (f : Lp ℝ 2 μ) :
    ContinuousAt (fun g : Lp ℝ 2 μ ↦ ∫ x, c x * (g : X → ℝ) x ^ 2 ∂μ) f := by
  have h_eq : (fun g : Lp ℝ 2 μ ↦ ∫ x, c x * (g : X → ℝ) x ^ 2 ∂μ) =
      (fun g ↦ weightedBilinearForm μ c g g) := by
    ext g
    have h_apply := weightedBilinearForm_apply μ c g g
    simp only [h_apply]
    congr 1
    ext x
    ring
  rw [h_eq]
  exact ContinuousAt.clm_apply
    (weightedBilinearForm μ c).continuous.continuousAt continuous_id.continuousAt

/-
Theorem: The continuous Rayleigh quotient is continuous at any non-zero function in L^2.
-/
omit [IsFiniteMeasure μ] in
theorem continuousRatio_continuous (c_cont : X → ℝ) [Fact (Continuous c_cont)]
    (f : Lp ℝ 2 μ) (hf : ‖f‖ > 0) :
    ContinuousAt (fun g : Lp ℝ 2 μ ↦ continuousRatio μ c_cont g) f := by
  have h_den_eq : (fun g : Lp ℝ 2 μ ↦ ∫ x, (g : X → ℝ) x ^ 2 ∂μ) = (fun g ↦ ‖g‖ ^ 2) := by
    ext g
    rw [← real_inner_self_eq_norm_sq g]
    rw [L2.inner_def]
    simp
  have h_num_cont : ContinuousAt (fun g : Lp ℝ 2 μ ↦ ∫ x, c_cont x * (g : X → ℝ) x ^ 2 ∂μ) f :=
    quadratic_form_continuous μ c_cont f
  have h_den_cont : ContinuousAt (fun g : Lp ℝ 2 μ ↦ ∫ x, (g : X → ℝ) x ^ 2 ∂μ) f := by
    rw [h_den_eq]
    exact continuous_norm.continuousAt.pow 2
  have h_den_pos : (fun g : Lp ℝ 2 μ ↦ ∫ x, (g : X → ℝ) x ^ 2 ∂μ) f > 0 := by
    have : (fun g : Lp ℝ 2 μ ↦ ∫ x, (g : X → ℝ) x ^ 2 ∂μ) f = ‖f‖ ^ 2 := by
      exact congr_fun h_den_eq f
    rw [this]
    exact sq_pos_of_pos hf
  have h_eq : (fun g : Lp ℝ 2 μ ↦
      (∫ x, c_cont x * (g : X → ℝ) x ^ 2 ∂μ) / (∫ x, (g : X → ℝ) x ^ 2 ∂μ)) =ᶠ[𝓝 f]
      (fun g ↦ continuousRatio μ c_cont g) := by
    have h_eventually_pos : ∀ᶠ g in 𝓝 f, (fun h : Lp ℝ 2 μ ↦ ∫ x, (h : X → ℝ) x ^ 2 ∂μ) g > 0 :=
      h_den_cont.eventually_const_lt h_den_pos
    filter_upwards [h_eventually_pos] with g hg_pos
    simp only [continuousRatio]
    have hg_ne : (∫ x, (g : X → ℝ) x ^ 2 ∂μ) ≠ 0 := ne_of_gt hg_pos
    rw [if_neg hg_ne]
  exact (ContinuousAt.div h_num_cont h_den_cont (ne_of_gt h_den_pos)).congr h_eq


/-- Mercer's Theorem (Refined with Tjeerd's feedback): -/
theorem mercer_theorem :
    ∃ (ι : Type*) (_ : Countable ι)
      (b : HilbertBasis ι 𝕜 (Lp V 2 μ))
      (σ : ι → ℝ),
      (∀ i, 0 ≤ σ i) ∧
      -- The basis elements are eigenfunctions of the integral operator
      (∀ i, (integralOperator μ : Lp V 2 μ →L[𝕜] Lp V 2 μ) (b i) = (σ i : 𝕜) • (b i)) ∧
      -- The kernel decomposition holds in the RKHS (using evaluation)
      -- (where φ_i is the representation of b_i in the RKHS)
      (∀ (x y : X) (v : V),
        kernel H x y v = ∑' i, (σ i : 𝕜) • ⟪v, (b i : X → V) y⟫_𝕜 • (b i : X → V) x) := by
  sorry

-- Sequence of RKHS spaces indexed by sieve parameter n
variable (H_seq : ℕ → Type*)
variable [∀ i, NormedAddCommGroup (H_seq i)] [∀ i, InnerProductSpace 𝕜 (H_seq i)]
variable [∀ i, CompleteSpace (H_seq i)] [∀ i, RKHS 𝕜 (H_seq i) X V]

-- Inclusion maps from each RKHS into L^2
variable (coeCLM : ∀ i, H_seq i →L[𝕜] Lp V 2 μ)

-- Projection operators onto each RKHS space
variable (projectionToRKHS : ∀ i, Lp V 2 μ →L[𝕜] H_seq i)

/-- Theorem: Strong convergence of the projected functions in L^2. -/
theorem projection_strong_convergence (f : Lp V 2 μ)
    (h_orthogonal : ∀ i (g : Lp V 2 μ) (h : H_seq i),
      ⟪coeCLM i (projectionToRKHS i g) - g, coeCLM i h⟫_𝕜 = 0)
    (h_mono : ∀ (i j : ℕ) (_ : i ≤ j) (x : H_seq i),
      ∃ y : H_seq j, coeCLM i x = coeCLM j y)
    (h_dense : ∀ (g : Lp V 2 μ) (ε : ℝ) (_ : 0 < ε),
      ∃ i, ∃ h : H_seq i, ‖coeCLM i h - g‖ < ε) :
    Filter.Tendsto (fun i ↦ ‖coeCLM i (projectionToRKHS i f) - f‖) Filter.atTop (nhds 0) := by
  sorry
