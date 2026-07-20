/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela, Gemini 3.5 Flash (Google DeepMind)
-/

import KrafftSieve.OptimalWeights
import KrafftSieve.MultiStarGraph

/-!
# Main Sieve Admissibility and Twin Prime Conjecture

This file connects the discrete optimal sieve weights to the Twin Prime Conjecture.
-/

namespace KrafftSieve
open scoped BigOperators

theorem multi_star_ansatz_implies_mu_min_lt_one (n : ℕ) (hn : 1000 ≤ n) : muMin n < 1 := by
  obtain ⟨A, hq1, h_ratio⟩ := exists_multi_star_with_mu_lt_one n hn
  have h_attainable : Ratio n (multiStarVector n A) ∈ attainableRatios n := by
    unfold attainableRatios
    simp only [Set.mem_setOf_eq]
    exact ⟨multiStarVector n A, hq1, rfl⟩
  have h_inf : muMin n ≤ Ratio n (multiStarVector n A) := by
    unfold muMin
    apply csInf_le
    · use 0
      intro r hr
      obtain ⟨l, hl_pos, rfl⟩ := hr
      unfold Ratio
      rw [if_neg (ne_of_gt hl_pos)]
      apply div_nonneg
      · have h_q2_sq : q2 n l = ∑ x ∈ Finset.range (q n), c n (x : ZMod (q n)) *
          (spatialVector n l x)^2 * Psi n (x : ZMod (q n)) := q2_eq_spatialVector_weighted_norm n l
        rw [h_q2_sq]
        refine Finset.sum_nonneg fun x _ => ?_
        refine mul_nonneg (mul_nonneg (c_nonneg n _) (sq_nonneg _)) ?_
        have h_psi : Psi n (x : ZMod (q n)) ≥ 0 := by unfold Psi; split_ifs <;> norm_num
        exact h_psi
      · exact le_of_lt hl_pos
    · exact h_attainable
  exact lt_of_le_of_lt h_inf h_ratio

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
Unconditional result: for all n >= 1000, muMin n < 1.
-/
theorem unconditional_mu_min_lt_one (n : ℕ) (hn : 1000 ≤ n) : muMin n < 1 := by
  exact multi_star_ansatz_implies_mu_min_lt_one n hn

/--
The Ultimate Goal: The Twin Prime Conjecture.
-/
theorem infinitely_many_twin_primes : {p : ℕ | Prime p ∧ Prime (p + 2)}.Infinite := by
  apply mu_min_lt_one_implies_tpc
  rw [Set.infinite_iff_exists_gt]
  intro B
  use max B 1000 + 1
  constructor
  · exact unconditional_mu_min_lt_one _ (by omega)
  · omega

#print axioms infinitely_many_twin_primes

end KrafftSieve
