/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela, Gemini 3.5 Flash (Google DeepMind)
-/

import KrafftSieve.OptimalWeights
import KrafftSieve.RKHSLimit

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
    (hn : ‖coeCLM_seq n (projectionToRKHS n f)‖ > 0)
    (h_quadrature : ∀ (h : H_seq n), ‖coeCLM_seq n h‖ > 0 →
      muMin n ≤ continuousRatio μ c_cont Psi_cont (coeCLM_seq n h)) :
    muMin n ≤ continuousRatio μ c_cont Psi_cont (coeCLM_seq n (projectionToRKHS n f)) := by
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
    (h_quadrature : ∀ n (h : H_seq n), ‖coeCLM_seq n h‖ > 0 →
      muMin n ≤ continuousRatio μ c_cont Psi_cont (coeCLM_seq n h)) :
    ∃ N_0 : ℕ, ∀ n ≥ N_0, muMin n < 1 := by
  -- Choose a continuous test function whose continuous Rayleigh quotient is < 1.
  obtain ⟨f, hf_pos, hf_lt⟩ := exists_continuous_ratio_lt_one μ c_cont Psi_cont h_dip
  -- The projected functions converge to `f` strongly in L².
  have h_sc : Filter.Tendsto
      (fun i ↦ ‖coeCLM_seq i (projectionToRKHS i f) - f‖) Filter.atTop (nhds 0) :=
    projection_strong_convergence μ H_seq coeCLM_seq projectionToRKHS f
      h_orthogonal h_mono h_dense
  -- Hence the Rayleigh quotients of the projections converge to that of `f`.
  have h_ratio_lim : Filter.Tendsto
      (fun n ↦ continuousRatio μ c_cont Psi_cont (coeCLM_seq n (projectionToRKHS n f)))
      Filter.atTop (nhds (continuousRatio μ c_cont Psi_cont f)) :=
    continuousRatio_limit μ c_cont Psi_cont f hf_pos
      (fun n ↦ coeCLM_seq n (projectionToRKHS n f)) h_sc
  -- `f` has positive L² norm (else its windowed norm would be zero).
  have hf_norm_pos : (0 : ℝ) < ‖f‖ := by
    rw [norm_pos_iff]
    intro h0
    have hfae : (f : X → ℝ) =ᵐ[μ] 0 := by rw [h0]; exact Lp.coeFn_zero ℝ 2 μ
    have hzero : (∫ x, (f : X → ℝ) x ^ 2 * Psi_cont x ∂μ) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hfae] with x hx
      simp [hx]
    rw [hzero] at hf_pos
    exact lt_irrefl 0 hf_pos
  -- The projections converge to `f`, so their norms converge to `‖f‖`.
  have h_tendsto : Filter.Tendsto (fun n ↦ coeCLM_seq n (projectionToRKHS n f))
      Filter.atTop (nhds f) := tendsto_iff_norm_sub_tendsto_zero.mpr h_sc
  have h_norm_tendsto : Filter.Tendsto
      (fun n ↦ ‖coeCLM_seq n (projectionToRKHS n f)‖) Filter.atTop (nhds ‖f‖) :=
    (continuous_norm.tendsto f).comp h_tendsto
  -- Eventually the ratio is < 1 and the projected norm is positive.
  have h_ev1 : ∀ᶠ n in Filter.atTop,
      continuousRatio μ c_cont Psi_cont (coeCLM_seq n (projectionToRKHS n f)) < 1 :=
    h_ratio_lim.eventually_lt_const hf_lt
  have h_ev2 : ∀ᶠ n in Filter.atTop,
      (0 : ℝ) < ‖coeCLM_seq n (projectionToRKHS n f)‖ :=
    h_norm_tendsto.eventually_const_lt hf_norm_pos
  obtain ⟨N_0, hN⟩ := Filter.eventually_atTop.mp (h_ev1.and h_ev2)
  refine ⟨N_0, fun n hn ↦ ?_⟩
  obtain ⟨h_lt, h_pos⟩ := hN n hn
  calc muMin n ≤ continuousRatio μ c_cont Psi_cont (coeCLM_seq n (projectionToRKHS n f)) :=
        h_quadrature n (projectionToRKHS n f) h_pos
    _ < 1 := h_lt

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
    (h_quadrature : ∀ n (h : H_seq n), ‖coeCLM_seq n h‖ > 0 →
      muMin n ≤ continuousRatio μ c_cont Psi_cont (coeCLM_seq n h)) :
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
    (h_quadrature : ∀ n (h : H_seq n), ‖coeCLM_seq n h‖ > 0 →
      muMin n ≤ continuousRatio μ c_cont Psi_cont (coeCLM_seq n h)) :
    {p : ℕ | Prime p ∧ Prime (p + 2)}.Infinite := by
  apply mu_min_lt_one_implies_tpc
  exact mu_min_infinite μ H_seq coeCLM_seq projectionToRKHS c_cont Psi_cont
    h_dip h_orthogonal h_mono h_dense h_quadrature

end KrafftSieve
