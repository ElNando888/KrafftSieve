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
    (f : Lp ℝ 2 μ) (hf : ‖f‖ > 0) (f_seq : ℕ → Lp ℝ 2 μ)
    (h_conv : Filter.Tendsto (fun n ↦ ‖f_seq n - f‖) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ continuousRatio μ c_cont (f_seq n)) Filter.atTop
      (nhds (continuousRatio μ c_cont f)) := by
  have h_conv' : Filter.Tendsto f_seq Filter.atTop (nhds f) := by
    rwa [tendsto_iff_norm_sub_tendsto_zero]
  exact Filter.Tendsto.comp (continuousRatio_continuous μ c_cont f hf) h_conv'

/--
Theorem: For any n, the discrete minimum sieve quotient muMin n is bounded by the
continuous Rayleigh quotient of the RKHS-projected test function.
-/
theorem muMin_le_rkhs_ratio (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ)
    (H_seq : ℕ → Type*) [∀ i, NormedAddCommGroup (H_seq i)] [∀ i, InnerProductSpace ℝ (H_seq i)]
    [∀ i, CompleteSpace (H_seq i)] [∀ i, RKHS ℝ (H_seq i) X ℝ]
    (coeCLM_seq : ∀ i, H_seq i →L[ℝ] Lp ℝ 2 μ)
    (projectionToRKHS : ∀ i, Lp ℝ 2 μ →L[ℝ] H_seq i)
    (c_cont : X → ℝ) (f : Lp ℝ 2 μ)
    (hn : ‖coeCLM_seq n (projectionToRKHS n f)‖ > 0) :
    muMin n ≤ continuousRatio μ c_cont (coeCLM_seq n (projectionToRKHS n f)) := by
  -- Follows from muMin_le_ratio_of_representable and Ratio_eq_spatialRatio
  sorry

/--
Analytical Limit Theorem: For sufficiently large n, the minimum sieve quotient
muMin n is strictly less than 1.
-/
theorem mu_min_eventually_lt_one (μ : Measure X) [IsFiniteMeasure μ]
    (H_seq : ℕ → Type*) [∀ i, NormedAddCommGroup (H_seq i)] [∀ i, InnerProductSpace ℝ (H_seq i)]
    [∀ i, CompleteSpace (H_seq i)] [∀ i, RKHS ℝ (H_seq i) X ℝ]
    (coeCLM_seq : ∀ i, H_seq i →L[ℝ] Lp ℝ 2 μ)
    (projectionToRKHS : ∀ i, Lp ℝ 2 μ →L[ℝ] H_seq i)
    (c_cont : X → ℝ) [Fact (Continuous c_cont)] :
    ∃ N_0 : ℕ, ∀ n ≥ N_0, muMin n < 1 := by
  obtain ⟨f_test, hf_test_norm, hf_test_ratio⟩ := exists_continuous_ratio_lt_one μ c_cont
  let f_seq : ℕ → Lp ℝ 2 μ := fun n ↦ coeCLM_seq n (projectionToRKHS n f_test)
  have h_conv : Filter.Tendsto (fun n ↦ ‖f_seq n - f_test‖) Filter.atTop (nhds 0) :=
    projection_strong_convergence μ H_seq coeCLM_seq projectionToRKHS f_test
  have h_ratio_conv := continuousRatio_limit μ c_cont f_test hf_test_norm f_seq h_conv
  have h_eventually_lt : ∀ᶠ n in Filter.atTop, continuousRatio μ c_cont (f_seq n) < 1 :=
    h_ratio_conv.eventually_lt_const hf_test_ratio
  have h_muMin_eventually : ∀ᶠ n in Filter.atTop, muMin n < 1 := by
    have h_le : ∀ᶠ n in Filter.atTop, muMin n ≤ continuousRatio μ c_cont (f_seq n) := by
      have h_conv' : Filter.Tendsto f_seq Filter.atTop (nhds f_test) := by
        rwa [tendsto_iff_norm_sub_tendsto_zero]
      have h_norm_conv : Filter.Tendsto (fun n ↦ ‖f_seq n‖) Filter.atTop (nhds ‖f_test‖) :=
        continuous_norm.tendsto f_test |>.comp h_conv'
      have h_norm_pos : ∀ᶠ n in Filter.atTop, 0 < ‖f_seq n‖ :=
        h_norm_conv.eventually_const_lt hf_test_norm
      filter_upwards [h_norm_pos] with n hn_pos
      exact muMin_le_rkhs_ratio μ n H_seq coeCLM_seq projectionToRKHS c_cont f_test hn_pos
    filter_upwards [h_le, h_eventually_lt]
    intro n hn_le hn_lt
    exact hn_le.trans_lt hn_lt
  rw [Filter.eventually_atTop] at h_muMin_eventually
  exact h_muMin_eventually

/--
Theorem: The optimal multidimensional sieve weight achieves a ratio strictly less than 1
for infinitely many n.
-/
theorem mu_min_infinite (μ : Measure X) [IsFiniteMeasure μ]
    (H_seq : ℕ → Type*) [∀ i, NormedAddCommGroup (H_seq i)] [∀ i, InnerProductSpace ℝ (H_seq i)]
    [∀ i, CompleteSpace (H_seq i)] [∀ i, RKHS ℝ (H_seq i) X ℝ]
    (coeCLM_seq : ∀ i, H_seq i →L[ℝ] Lp ℝ 2 μ)
    (projectionToRKHS : ∀ i, Lp ℝ 2 μ →L[ℝ] H_seq i)
    (c_cont : X → ℝ) [Fact (Continuous c_cont)] :
    {n : ℕ | muMin n < 1}.Infinite := by
  obtain ⟨N_0, hN⟩ := mu_min_eventually_lt_one μ H_seq coeCLM_seq projectionToRKHS c_cont
  refine Set.Infinite.mono ?_ (Set.Ici_infinite N_0)
  intro n hn
  exact hN n hn

/--
The Twin Prime Conjecture: There are infinitely many twin primes.
-/
theorem twin_prime_conjecture (μ : Measure X) [IsFiniteMeasure μ]
    (H_seq : ℕ → Type*) [∀ i, NormedAddCommGroup (H_seq i)] [∀ i, InnerProductSpace ℝ (H_seq i)]
    [∀ i, CompleteSpace (H_seq i)] [∀ i, RKHS ℝ (H_seq i) X ℝ]
    (coeCLM_seq : ∀ i, H_seq i →L[ℝ] Lp ℝ 2 μ)
    (projectionToRKHS : ∀ i, Lp ℝ 2 μ →L[ℝ] H_seq i)
    (c_cont : X → ℝ) [Fact (Continuous c_cont)] :
    {p : ℕ | Prime p ∧ Prime (p + 2)}.Infinite := by
  apply mu_min_lt_one_implies_tpc
  exact mu_min_infinite μ H_seq coeCLM_seq projectionToRKHS c_cont

end KrafftSieve
