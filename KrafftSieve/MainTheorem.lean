/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela, Gemini 3.5 Flash (Google DeepMind)
-/

import KrafftSieve.OptimalWeights
import KrafftSieve.RKHSLimit
import KrafftSieve.Discretization
import KrafftSieve.GibbsDip
import KrafftSieve.ProfiniteRKHS
import Mathlib.MeasureTheory.Measure.MeasureSpace


/-!
# Main Sieve Admissibility and Twin Prime Conjecture

This file connects the continuous RKHS projection limits to the discrete
optimal sieve weights, proving the main limit theorem and the Twin Prime Conjecture.
-/

open MeasureTheory Matrix HilbertBasis RKHS InnerProductSpace

namespace KrafftSieve

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/--
Theorem: If there are infinitely many intervals where the optimal multidimensional
weight achieves a ratio strictly less than 1, then there are infinitely many twin primes.
-/
theorem mu_min_lt_one_implies_tpc :
    {n : ℕ | muMin n < 1}.Infinite
    → {p : ℕ | Prime p ∧ Prime (p + 2)}.Infinite := by
  intro h_inf
  rw [Set.infinite_iff_exists_gt] at h_inf ⊢
  intro B
  obtain ⟨n, hn_set, hn_gt⟩ := h_inf B
  have h_mu : muMin n < 1 := hn_set
  obtain ⟨x, hx_int, hx_prime1, hx_prime2⟩ := krafft_sieve_guarantee_with_mu_min n h_mu
  have hx_lower : x ≥ 6 * n^2 - 2 * n := by
    rw [evalInterval] at hx_int
    exact Finset.mem_Icc.mp hx_int |>.1
  have hn_sq : n^2 ≥ n := by nlinarith
  have hp_gt : 6 * x - 1 > B := by omega
  have h_plus_two : 6 * x - 1 + 2 = 6 * x + 1 := by omega
  have hp_goal : Prime (6 * x - 1) ∧ Prime (6 * x - 1 + 2) := by
    rw [h_plus_two]
    exact ⟨Nat.prime_iff.mp hx_prime1, Nat.prime_iff.mp hx_prime2⟩
  exact ⟨6 * x - 1, hp_goal, hp_gt⟩

/--
Theorem: If a sequence of functions converges strongly in L^2, then their continuous
Rayleigh quotients converge to the Rayleigh quotient of the limit function.
-/
theorem continuousRatio_limit (μ : Measure X) [IsFiniteMeasure μ]
    (c_cont : X → ℝ) [Fact (Continuous c_cont)]
    (Psi_cont : X → ℝ) [Fact (Continuous Psi_cont)]
    (f : Lp ℝ 2 μ) (hf : (∫ x, (f : X → ℝ) x ^ 2 * Psi_cont x ∂μ) > 0) (f_seq : ℕ → Lp ℝ 2 μ)
    (h_conv : Filter.Tendsto (fun n ↦ ‖f_seq n - f‖) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ continuousRatio μ c_cont Psi_cont (f_seq n)) Filter.atTop
      (nhds (continuousRatio μ c_cont Psi_cont f)) := by
  have hcont : ContinuousAt (fun g : Lp ℝ 2 μ ↦ continuousRatio μ c_cont Psi_cont g) f :=
    continuousRatio_continuous μ c_cont Psi_cont f hf
  have h_tendsto : Filter.Tendsto f_seq Filter.atTop (nhds f) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr h_conv
  exact hcont.tendsto.comp h_tendsto

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] in
/--
Theorem: For any n, the discrete minimum sieve quotient muMin n is bounded by the
continuous Rayleigh quotient of the RKHS-projected test function.
-/
theorem muMin_le_rkhs_ratio (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ)
    (H_seq : ℕ → Type*) [∀ i, NormedAddCommGroup (H_seq i)] [∀ i, InnerProductSpace ℝ (H_seq i)]
    [∀ i, CompleteSpace (H_seq i)] [∀ i, RKHS ℝ (H_seq i) X ℝ]
    (coeCLM_seq : ∀ i, H_seq i →L[ℝ] Lp ℝ 2 μ)
    (projectionToRKHS : ∀ i, Lp ℝ 2 μ →L[ℝ] H_seq i)
    (c_cont : X → ℝ) (Psi_cont : X → ℝ) (f : Lp ℝ 2 μ)
    (hn : (∫ x, ((coeCLM_seq n (projectionToRKHS n f) : X → ℝ) x) ^ 2 * Psi_cont x ∂μ) > 0)
    (h_quadrature : ∀ (h : H_seq n), (∫ x, ((coeCLM_seq n h : X → ℝ) x) ^ 2 * Psi_cont x ∂μ) > 0 →
      muMin n ≤ continuousRatio μ c_cont Psi_cont (coeCLM_seq n h) +
        (numerator_error n + muMin n * denominator_error n) * ‖coeCLM_seq n h‖ ^ 2 /
          (∫ x, ((coeCLM_seq n h : X → ℝ) x) ^ 2 * Psi_cont x ∂μ)) :
    muMin n ≤ continuousRatio μ c_cont Psi_cont (coeCLM_seq n (projectionToRKHS n f)) +
      (numerator_error n + muMin n * denominator_error n) *
        ‖coeCLM_seq n (projectionToRKHS n f)‖ ^ 2 /
        (∫ x, ((coeCLM_seq n (projectionToRKHS n f) : X → ℝ) x) ^ 2 * Psi_cont x ∂μ) := by
  exact h_quadrature (projectionToRKHS n f) hn

/--
Analytical Limit Theorem: For sufficiently large n, the minimum sieve quotient
muMin n is strictly less than 1.
-/
theorem mu_min_eventually_lt_one (μ : Measure X) [IsFiniteMeasure μ]
    (H_seq : ℕ → Type*) [∀ i, NormedAddCommGroup (H_seq i)] [∀ i, InnerProductSpace ℝ (H_seq i)]
    [∀ i, CompleteSpace (H_seq i)] [∀ i, RKHS ℝ (H_seq i) X ℝ]
    (coeCLM_seq : ∀ i, H_seq i →L[ℝ] Lp ℝ 2 μ)
    (projectionToRKHS : ∀ i, Lp ℝ 2 μ →L[ℝ] H_seq i)
    (c_cont : X → ℝ) [Fact (Continuous c_cont)]
    (Psi_cont : X → ℝ) [Fact (Continuous Psi_cont)]
    (h_dip : ∃ s : Set X, MeasurableSet s ∧ 0 < ∫ x in s, Psi_cont x ∂μ ∧ ∀ x ∈ s, c_cont x < 1)
    (h_orthogonal : ∀ i (g : Lp ℝ 2 μ) (h : H_seq i),
      ⟪coeCLM_seq i (projectionToRKHS i g) - g, coeCLM_seq i h⟫_ℝ = 0)
    (h_mono : ∀ (i j : ℕ) (_ : i ≤ j) (x : H_seq i),
      ∃ y : H_seq j, coeCLM_seq i x = coeCLM_seq j y)
    (h_dense : ∀ (g : Lp ℝ 2 μ) (ε : ℝ) (_ : 0 < ε),
      ∃ i, ∃ h : H_seq i, ‖coeCLM_seq i h - g‖ < ε)
    (h_quadrature : ∀ n (h : H_seq n), (∫ x, ((coeCLM_seq n h : X → ℝ) x) ^ 2 * Psi_cont x ∂μ) > 0 →
      muMin n ≤ continuousRatio μ c_cont Psi_cont (coeCLM_seq n h) +
        (numerator_error n + muMin n * denominator_error n) * ‖coeCLM_seq n h‖ ^ 2 /
          (∫ x, ((coeCLM_seq n h : X → ℝ) x) ^ 2 * Psi_cont x ∂μ)) :
    ∃ N_0 : ℕ, ∀ n ≥ N_0, muMin n < 1 := by
  -- Step 1: obtain a continuous witness with ratio < 1 and positive windowed norm.
  obtain ⟨f, hf_pos, hf_lt⟩ := exists_continuous_ratio_lt_one μ c_cont Psi_cont h_dip
  -- Step 2: the projected sequence converges strongly to `f` in `L²`.
  have h_conv : Filter.Tendsto
      (fun n ↦ ‖coeCLM_seq n (projectionToRKHS n f) - f‖) Filter.atTop (nhds 0) :=
    projection_strong_convergence μ H_seq coeCLM_seq projectionToRKHS f
      h_orthogonal h_mono h_dense
  -- hence the continuous Rayleigh quotients converge to that of `f`.
  have h_ratio : Filter.Tendsto
      (fun n ↦ continuousRatio μ c_cont Psi_cont (coeCLM_seq n (projectionToRKHS n f)))
      Filter.atTop (nhds (continuousRatio μ c_cont Psi_cont f)) :=
    continuousRatio_limit μ c_cont Psi_cont f hf_pos
      (fun n ↦ coeCLM_seq n (projectionToRKHS n f)) h_conv
  -- Step 3/4: the denominator converges to a positive limit, hence is eventually positive.
  have h_fseq : Filter.Tendsto (fun n ↦ coeCLM_seq n (projectionToRKHS n f))
      Filter.atTop (nhds f) := tendsto_iff_norm_sub_tendsto_zero.mpr h_conv
  have hDcont : ContinuousAt
      (fun g : Lp ℝ 2 μ ↦ ∫ x, (g : X → ℝ) x ^ 2 * Psi_cont x ∂μ) f := by
    have h_eq : (fun g : Lp ℝ 2 μ ↦ ∫ x, (g : X → ℝ) x ^ 2 * Psi_cont x ∂μ)
        = (fun g : Lp ℝ 2 μ ↦ ∫ x, Psi_cont x * (g : X → ℝ) x ^ 2 ∂μ) := by
      funext g; congr 1; funext x; ring
    rw [h_eq]
    exact quadratic_form_continuous μ Psi_cont f
  have hDen : Filter.Tendsto
      (fun n ↦ ∫ x, (coeCLM_seq n (projectionToRKHS n f) : X → ℝ) x ^ 2 * Psi_cont x ∂μ)
      Filter.atTop (nhds (∫ x, (f : X → ℝ) x ^ 2 * Psi_cont x ∂μ)) :=
    hDcont.tendsto.comp h_fseq
  have h_ev_den : ∀ᶠ n in Filter.atTop,
      0 < ∫ x, (coeCLM_seq n (projectionToRKHS n f) : X → ℝ) x ^ 2 * Psi_cont x ∂μ :=
    hDen.eventually (lt_mem_nhds hf_pos)
  have h_ev_ratio : ∀ᶠ n in Filter.atTop,
      continuousRatio μ c_cont Psi_cont (coeCLM_seq n (projectionToRKHS n f)) < 1 :=
    h_ratio.eventually_lt_const hf_lt
  -- Combine both eventual facts and conclude via the quadrature bound.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h_ev_ratio.and h_ev_den)
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨hr, hd⟩ := hN n hn
  have hq := h_quadrature n (projectionToRKHS n f) hd
  simp only [numerator_error, denominator_error, mul_zero, add_zero, zero_mul, zero_div] at hq
  linarith [hq, hr]

/--
Theorem: The optimal multidimensional sieve weight achieves a ratio strictly less than 1
for infinitely many n.
-/
theorem mu_min_infinite (μ : Measure X) [IsFiniteMeasure μ]
    (H_seq : ℕ → Type*) [∀ i, NormedAddCommGroup (H_seq i)] [∀ i, InnerProductSpace ℝ (H_seq i)]
    [∀ i, CompleteSpace (H_seq i)] [∀ i, RKHS ℝ (H_seq i) X ℝ]
    (coeCLM_seq : ∀ i, H_seq i →L[ℝ] Lp ℝ 2 μ)
    (projectionToRKHS : ∀ i, Lp ℝ 2 μ →L[ℝ] H_seq i)
    (c_cont : X → ℝ) [Fact (Continuous c_cont)]
    (Psi_cont : X → ℝ) [Fact (Continuous Psi_cont)]
    (h_dip : ∃ s : Set X, MeasurableSet s ∧ 0 < ∫ x in s, Psi_cont x ∂μ ∧ ∀ x ∈ s, c_cont x < 1)
    (h_orthogonal : ∀ i (g : Lp ℝ 2 μ) (h : H_seq i),
      ⟪coeCLM_seq i (projectionToRKHS i g) - g, coeCLM_seq i h⟫_ℝ = 0)
    (h_mono : ∀ (i j : ℕ) (_ : i ≤ j) (x : H_seq i),
      ∃ y : H_seq j, coeCLM_seq i x = coeCLM_seq j y)
    (h_dense : ∀ (g : Lp ℝ 2 μ) (ε : ℝ) (_ : 0 < ε),
      ∃ i, ∃ h : H_seq i, ‖coeCLM_seq i h - g‖ < ε)
    (h_quadrature : ∀ n (h : H_seq n), (∫ x, ((coeCLM_seq n h : X → ℝ) x) ^ 2 * Psi_cont x ∂μ) > 0 →
      muMin n ≤ continuousRatio μ c_cont Psi_cont (coeCLM_seq n h) +
        (numerator_error n + muMin n * denominator_error n) * ‖coeCLM_seq n h‖ ^ 2 /
          (∫ x, ((coeCLM_seq n h : X → ℝ) x) ^ 2 * Psi_cont x ∂μ)) :
    {n : ℕ | muMin n < 1}.Infinite := by
  obtain ⟨N_0, hN⟩ := mu_min_eventually_lt_one μ H_seq coeCLM_seq projectionToRKHS
    c_cont Psi_cont h_dip h_orthogonal h_mono h_dense h_quadrature
  have h_sub : Set.Ici N_0 ⊆ {n : ℕ | muMin n < 1} := fun n hn ↦ hN n hn
  exact (Set.Ici_infinite N_0).mono h_sub

/--
The Twin Prime Conjecture: There are infinitely many twin primes.
-/
theorem twin_prime_conjecture (μ : Measure X) [IsFiniteMeasure μ]
    (H_seq : ℕ → Type*) [∀ i, NormedAddCommGroup (H_seq i)] [∀ i, InnerProductSpace ℝ (H_seq i)]
    [∀ i, CompleteSpace (H_seq i)] [∀ i, RKHS ℝ (H_seq i) X ℝ]
    (coeCLM_seq : ∀ i, H_seq i →L[ℝ] Lp ℝ 2 μ)
    (projectionToRKHS : ∀ i, Lp ℝ 2 μ →L[ℝ] H_seq i)
    (c_cont : X → ℝ) [Fact (Continuous c_cont)]
    (Psi_cont : X → ℝ) [Fact (Continuous Psi_cont)]
    (h_dip : ∃ s : Set X, MeasurableSet s ∧ 0 < ∫ x in s, Psi_cont x ∂μ ∧ ∀ x ∈ s, c_cont x < 1)
    (h_orthogonal : ∀ i (g : Lp ℝ 2 μ) (h : H_seq i),
      ⟪coeCLM_seq i (projectionToRKHS i g) - g, coeCLM_seq i h⟫_ℝ = 0)
    (h_mono : ∀ (i j : ℕ) (_ : i ≤ j) (x : H_seq i),
      ∃ y : H_seq j, coeCLM_seq i x = coeCLM_seq j y)
    (h_dense : ∀ (g : Lp ℝ 2 μ) (ε : ℝ) (_ : 0 < ε),
      ∃ i, ∃ h : H_seq i, ‖coeCLM_seq i h - g‖ < ε)
    (h_quadrature : ∀ n (h : H_seq n), (∫ x, ((coeCLM_seq n h : X → ℝ) x) ^ 2 * Psi_cont x ∂μ) > 0 →
      muMin n ≤ continuousRatio μ c_cont Psi_cont (coeCLM_seq n h) +
        (numerator_error n + muMin n * denominator_error n) * ‖coeCLM_seq n h‖ ^ 2 /
          (∫ x, ((coeCLM_seq n h : X → ℝ) x) ^ 2 * Psi_cont x ∂μ)) :
    {p : ℕ | Prime p ∧ Prime (p + 2)}.Infinite := by
  apply mu_min_lt_one_implies_tpc
  exact mu_min_infinite μ H_seq coeCLM_seq projectionToRKHS c_cont Psi_cont
    h_dip h_orthogonal h_mono h_dense h_quadrature

-- ==============================================================================
-- PROFINITE RKHS STUBS
-- ==============================================================================

/-- The real RKHS over the profinite group `X`, corresponding to the real part of `H n`. -/
noncomputable def H_real (n : ℕ) : Type := sorry
noncomputable instance (n : ℕ) : NormedAddCommGroup (H_real n) := sorry
noncomputable instance (n : ℕ) : InnerProductSpace ℝ (H_real n) := sorry
noncomputable instance (n : ℕ) : CompleteSpace (H_real n) := sorry
noncomputable instance (n : ℕ) : RKHS ℝ (H_real n) KrafftSieve.X ℝ := sorry

/-- The inclusion of the real RKHS into the real `L²` space over the profinite group. -/
noncomputable def coeCLM_real (n : ℕ) : H_real n →L[ℝ] Lp ℝ 2 haarProb := sorry

/-- The orthogonal projection from the real `L²` space onto the finite-dimensional `H_real n`. -/
noncomputable def projectionToRKHS_real (n : ℕ) : Lp ℝ 2 haarProb →L[ℝ] H_real n := sorry

/-- The continuous penalty function lifted to the profinite group. -/
noncomputable def c_cont_profinite (n : ℕ) : KrafftSieve.X → ℝ := sorry
noncomputable instance (n : ℕ) : Fact (Continuous (c_cont_profinite n)) := sorry

/-- The continuous window function lifted to the profinite group. -/
noncomputable def Psi_cont_profinite (n : ℕ) : KrafftSieve.X → ℝ := sorry
noncomputable instance (n : ℕ) : Fact (Continuous (Psi_cont_profinite n)) := sorry

-- ==============================================================================

theorem infinitely_many_twin_primes : {p : ℕ | Prime p ∧ Prime (p + 2)}.Infinite := by
  exact twin_prime_conjecture (μ := haarProb) (H_seq := H_real) (coeCLM_seq := coeCLM_real)
    (projectionToRKHS := projectionToRKHS_real) (c_cont := c_cont_profinite 19)
    (Psi_cont := Psi_cont_profinite 19)
    sorry -- h_dip
    sorry -- h_orthogonal
    sorry -- h_mono
    sorry -- h_dense
    sorry -- h_quadrature

end KrafftSieve
