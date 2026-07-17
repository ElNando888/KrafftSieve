/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela, Gemini 3.5 Flash (Google DeepMind)
-/

import KrafftSieve.OptimalWeights

/-!
# Main Sieve Admissibility and Twin Prime Conjecture

This file connects the discrete optimal sieve weights to the Twin Prime Conjecture.
-/

namespace KrafftSieve
open scoped BigOperators



theorem all_ones_vector_implies_mu_min_lt_one (n : ℕ) (hn : 1 ≤ n)
    (h_q1_pos : q1 n (allOnesVector n) > 0)
    (h_ratio : q2 n (allOnesVector n) < q1 n (allOnesVector n)) :
    muMin n < 1 := by
  have h_attainable : Ratio n (allOnesVector n) ∈ attainableRatios n := by
    unfold attainableRatios
    simp only [Set.mem_setOf_eq]
    exact ⟨allOnesVector n, h_q1_pos, rfl⟩
  have h_inf : muMin n ≤ Ratio n (allOnesVector n) := by
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
  have h_ratio_eval : Ratio n (allOnesVector n) < 1 := by
    unfold Ratio
    rw [if_neg (ne_of_gt h_q1_pos)]
    exact (div_lt_one h_q1_pos).mpr h_ratio
  exact lt_of_le_of_lt h_inf h_ratio_eval


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

end KrafftSieve
