/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela, Gemini 3.5 Flash (Google DeepMind)
-/

import KrafftSieve.OptimalWeights
import KrafftSieve.RidgeGraph
import KrafftSieve.PhaseLock

/-!
# Main Sieve Admissibility and Twin Prime Conjecture

This file connects the discrete optimal sieve weights to the Twin Prime Conjecture.
-/

namespace KrafftSieve
open scoped BigOperators


lemma matrix1_eq_massMatrixEntry (n : ℕ) (hn : 1 ≤ n) (S T : Finset (Fin (w n))) :
    matrix1 n S T = massMatrixEntry n S T := by
  unfold matrix1 massMatrixEntry
  have hsub : evalInterval n ⊆ Finset.range (q n) := by
    intro y hy
    rw [Finset.mem_range]
    exact lt_of_le_of_lt (Finset.mem_Icc.mp hy).2 (q_bound n hn)
  have hval : ∀ y ∈ Finset.range (q n), ((y : ZMod (q n)).val = y) :=
    fun y hy => ZMod.val_natCast_of_lt (Finset.mem_range.mp hy)
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro x hx
    have hxe : (x : ZMod (q n)).val ∈ evalInterval n := by
      rw [hval x (hsub hx)]; exact hx
    have h_psi : Psi n (x : ZMod (q n)) = 1 := by
      unfold Psi; rw [if_pos hxe]
    have h_basis1 : basisCos n S ↑x = basisFunction n S x := by
      unfold basisCos basisFunction
      apply Finset.prod_congr rfl
      intro i _
      have : ((x : ZMod (q n)).val : ℝ) = (x : ℝ) := by
        have h1 : (x : ZMod (q n)).val = x := hval x (hsub hx)
        rw [h1]
      simp only [this]
      ring_nf
    have h_basis2 : basisCos n T ↑x = basisFunction n T x := by
      unfold basisCos basisFunction
      apply Finset.prod_congr rfl
      intro i _
      have : ((x : ZMod (q n)).val : ℝ) = (x : ℝ) := by
        have h1 : (x : ZMod (q n)).val = x := hval x (hsub hx)
        rw [h1]
      simp only [this]
      ring_nf
    rw [h_psi, mul_one, h_basis1, h_basis2]
  · intro y hy hy'
    have hz : Psi n (y : ZMod (q n)) = 0 := by
      unfold Psi; rw [if_neg]; rw [hval y hy]; exact hy'
    rw [hz, mul_zero]

lemma matrix2_eq_penaltyMatrixEntry (n : ℕ) (hn : 1 ≤ n) (S T : Finset (Fin (w n))) :
    matrix2 n S T = penaltyMatrixEntry n S T := by
  unfold matrix2 penaltyMatrixEntry
  have hsub : evalInterval n ⊆ Finset.range (q n) := by
    intro y hy
    rw [Finset.mem_range]
    exact lt_of_le_of_lt (Finset.mem_Icc.mp hy).2 (q_bound n hn)
  have hval : ∀ y ∈ Finset.range (q n), ((y : ZMod (q n)).val = y) :=
    fun y hy => ZMod.val_natCast_of_lt (Finset.mem_range.mp hy)
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro x hx
    have hxe : (x : ZMod (q n)).val ∈ evalInterval n := by
      rw [hval x (hsub hx)]; exact hx
    have h_psi : Psi n (x : ZMod (q n)) = 1 := by
      unfold Psi; rw [if_pos hxe]
    have h_basis1 : basisCos n S ↑x = basisFunction n S x := by
      unfold basisCos basisFunction
      apply Finset.prod_congr rfl
      intro i _
      have : ((x : ZMod (q n)).val : ℝ) = (x : ℝ) := by
        have h1 : (x : ZMod (q n)).val = x := hval x (hsub hx)
        rw [h1]
      simp only [this]
      ring_nf
    have h_basis2 : basisCos n T ↑x = basisFunction n T x := by
      unfold basisCos basisFunction
      apply Finset.prod_congr rfl
      intro i _
      have : ((x : ZMod (q n)).val : ℝ) = (x : ℝ) := by
        have h1 : (x : ZMod (q n)).val = x := hval x (hsub hx)
        rw [h1]
      simp only [this]
      ring_nf
    rw [h_psi, mul_one, h_basis1, h_basis2]
  · intro y hy hy'
    have hz : Psi n (y : ZMod (q n)) = 0 := by
      unfold Psi; rw [if_neg]; rw [hval y hy]; exact hy'
    rw [hz, mul_zero]

theorem ridge_graph_ansatz_implies_mu_min_lt_one (n : ℕ) (hn : 1 ≤ n)
    (C : Finset (Finset (Fin (w n))))
    (h_clique : (ridgeGraph n).IsClique (C : Set (Finset (Fin (w n)))))
    (h_offdiag : ∀ S ∈ C, ∀ T ∈ C, S ≠ T → penaltyMatrixEntry n S T ≤ 0)
    (h_large : (C.card : ℝ) >
      1 + 2 * (∑ x ∈ evalInterval n, c n (x : ZMod (q n))) / (evalInterval n).card) :
    muMin n < 1 := by
  let lambda : Idx n → ℝ := fun S => if S ∈ C then 1 else 0
  have h_q1 : q1 n lambda = testMass n C := by
    unfold q1 testMass
    have hsub : C ⊆ Finset.univ.powerset := fun _ _ =>
      Finset.mem_powerset.mpr (fun _ _ => Finset.mem_univ _)
    have h_sum : ∑ S ∈ Finset.univ.powerset, ∑ T ∈ Finset.univ.powerset,
        lambda S * matrix1 n S T * lambda T =
        ∑ S ∈ C, ∑ T ∈ C, lambda S * matrix1 n S T * lambda T := by
      rw [← Finset.sum_subset hsub (fun x _ hx => by
        have : lambda x = 0 := if_neg hx
        simp only [this, zero_mul]
        exact Finset.sum_const_zero)]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← Finset.sum_subset hsub (fun y _ hy => by
        have : lambda y = 0 := if_neg hy
        simp only [this, mul_zero])]
    rw [h_sum]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    refine Finset.sum_congr rfl (fun T hT => ?_)
    have hlS : lambda S = 1 := if_pos hS
    have hlT : lambda T = 1 := if_pos hT
    rw [hlS, hlT, one_mul, mul_one]
    exact matrix1_eq_massMatrixEntry n hn S T
  have h_q2 : q2 n lambda = testPenalty n C := by
    unfold q2 testPenalty
    have hsub : C ⊆ Finset.univ.powerset := fun _ _ =>
      Finset.mem_powerset.mpr (fun _ _ => Finset.mem_univ _)
    have h_sum : ∑ S ∈ Finset.univ.powerset, ∑ T ∈ Finset.univ.powerset,
        lambda S * matrix2 n S T * lambda T =
        ∑ S ∈ C, ∑ T ∈ C, lambda S * matrix2 n S T * lambda T := by
      rw [← Finset.sum_subset hsub (fun x _ hx => by
        have : lambda x = 0 := if_neg hx
        simp only [this, zero_mul]
        exact Finset.sum_const_zero)]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← Finset.sum_subset hsub (fun y _ hy => by
        have : lambda y = 0 := if_neg hy
        simp only [this, mul_zero])]
    rw [h_sum]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    refine Finset.sum_congr rfl (fun T hT => ?_)
    have hlS : lambda S = 1 := if_pos hS
    have hlT : lambda T = 1 := if_pos hT
    rw [hlS, hlT, one_mul, mul_one]
    exact matrix2_eq_penaltyMatrixEntry n hn S T
  have h_mass := testMass_lower_bound n C h_clique
  have h_mass_pos : 0 < testMass n C := by
    have hp : (evalInterval n).card > 0 := by
      unfold evalInterval
      have : 6 * n ^ 2 - 2 * n < 6 * n ^ 2 + 10 * n + 4 := by omega
      exact Finset.card_pos.mpr (Finset.nonempty_Ico.mpr this)
    have hp_r : ((evalInterval n).card : ℝ) > 0 := Nat.cast_pos.mpr hp
    have h_thresh : 0 < ridgeThreshold n := by
      unfold ridgeThreshold; positivity
    have h_div_nonneg : 0 ≤
        2 * (∑ x ∈ evalInterval n, c n (x : ZMod (q n))) / (evalInterval n).card := by
      refine div_nonneg ?_ hp_r.le
      refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => c_nonneg n (x : ZMod (q n)))
    have hc : (C.card : ℝ) > 1 := by linarith
    have : 0 < (C.card : ℝ) * ((C.card : ℝ) - 1) * ridgeThreshold n := by positivity
    linarith
  have hq1_pos : q1 n lambda > 0 := by
    rw [h_q1]; exact h_mass_pos
  have h_ratio : Ratio n lambda < 1 := by
    unfold Ratio
    rw [if_neg (ne_of_gt hq1_pos)]
    rw [h_q1, h_q2]
    exact rayleigh_quotient_bound n C h_clique h_offdiag h_large
  have h_attainable : Ratio n lambda ∈ attainableRatios n := by
    unfold attainableRatios
    simp only [Set.mem_setOf_eq]
    exact ⟨lambda, hq1_pos, rfl⟩
  have h_inf : muMin n ≤ Ratio n lambda := by
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
This relies on the Phase 6 Main Theorem which constructs a large negative clique.
-/
theorem unconditional_mu_min_lt_one (n : ℕ) (hn : 1000 ≤ n) : muMin n < 1 := by
  obtain ⟨C, h_clique, h_offdiag, h_large⟩ := exists_large_ridge_clique n hn
  exact ridge_graph_ansatz_implies_mu_min_lt_one n (by omega) C h_clique h_offdiag h_large

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

end KrafftSieve
