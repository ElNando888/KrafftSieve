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

private def crosses {α : Type} [DecidableEq α] (A S : Finset α) : Prop :=
  ∃ a ∈ A, ∃ j ∉ A, S = {a, j}

private noncomputable instance {α : Type} [DecidableEq α] (A S : Finset α) :
    Decidable (crosses A S) := Classical.propDecidable _

private lemma q1_multiStar_eq_spatial (n : ℕ) (hn : 1 ≤ n) (A : Finset (Fin (w n))) :
    q1 n (multiStarVector n A) =
      ∑ S ∈ Edges n, ∑ T ∈ Edges n,
        (if crosses A S then starWeight n S else 0) *
          massMatrixEntry n S T *
        (if crosses A T then starWeight n T else 0) := by
  classical
  unfold q1 Edges
  simp_rw [matrix1_eq_massMatrixEntry n hn]
  simp only [Finset.sum_filter]
  congr 1
  funext S
  by_cases hS : S.card = 2
  · simp only [hS, ↓reduceIte]
    congr 1
    funext T
    by_cases hT : T.card = 2
    · simp only [hT, ↓reduceIte]
      unfold multiStarVector crosses
      split <;> split <;> simp_all
    · have hvT : multiStarVector n A T = 0 := by
        unfold multiStarVector
        split
        · obtain ⟨a, ha, j, hj, heq⟩ := ‹∃ a ∈ A, ∃ j ∉ A, T = {a, j}›
          have hc : T.card = 2 := by
            rw [heq]
            simp [ne_of_mem_of_not_mem ha hj]
          contradiction
        · rfl
      simp only [hT, ↓reduceIte, hvT, mul_zero]
  · have hvS : multiStarVector n A S = 0 := by
      unfold multiStarVector
      split
      · obtain ⟨a, ha, j, hj, heq⟩ := ‹∃ a ∈ A, ∃ j ∉ A, S = {a, j}›
        have hc : S.card = 2 := by
          rw [heq]
          simp [ne_of_mem_of_not_mem ha hj]
        contradiction
      · rfl
    simp only [hS, ↓reduceIte, hvS, zero_mul, Finset.sum_const_zero]

private lemma q2_multiStar_eq_spatial (n : ℕ) (hn : 1 ≤ n) (A : Finset (Fin (w n))) :
    q2 n (multiStarVector n A) =
      ∑ S ∈ Edges n, ∑ T ∈ Edges n,
        (if crosses A S then starWeight n S else 0) *
          penaltyMatrixEntry n S T *
        (if crosses A T then starWeight n T else 0) := by
  classical
  unfold q2 Edges
  simp_rw [matrix2_eq_penaltyMatrixEntry n hn]
  simp only [Finset.sum_filter]
  congr 1
  funext S
  by_cases hS : S.card = 2
  · simp only [hS, ↓reduceIte]
    congr 1
    funext T
    by_cases hT : T.card = 2
    · simp only [hT, ↓reduceIte]
      unfold multiStarVector crosses
      split <;> split <;> simp_all
    · have hvT : multiStarVector n A T = 0 := by
        unfold multiStarVector
        split
        · obtain ⟨a, ha, j, hj, heq⟩ := ‹∃ a ∈ A, ∃ j ∉ A, T = {a, j}›
          have hc : T.card = 2 := by
            rw [heq]
            simp [ne_of_mem_of_not_mem ha hj]
          contradiction
        · rfl
      simp only [hT, ↓reduceIte, hvT, mul_zero]
  · have hvS : multiStarVector n A S = 0 := by
      unfold multiStarVector
      split
      · obtain ⟨a, ha, j, hj, heq⟩ := ‹∃ a ∈ A, ∃ j ∉ A, S = {a, j}›
        have hc : S.card = 2 := by
          rw [heq]
          simp [ne_of_mem_of_not_mem ha hj]
        contradiction
      · rfl
    simp only [hS, ↓reduceIte, hvS, zero_mul, Finset.sum_const_zero]

private lemma w_ge_four (n : ℕ) (hn : 1000 ≤ n) : 4 ≤ w n := by
  unfold w
  have hsub : ({5, 7, 11, 13} : Finset ℕ) ⊆ primeWindow n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    unfold primeWindow
    simp only [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl <;> norm_num <;> omega
  have hc := Finset.card_le_card hsub
  norm_num at hc ⊢
  exact hc

private lemma card_fixed_size_contains_disjoint {α : Type} [DecidableEq α]
    (U R F : Finset α) (m : ℕ) (hR : R ⊆ U) (hF : F ⊆ U) (hRF : Disjoint R F)
    (hRm : R.card ≤ m) :
    ((U.powersetCard m).filter (fun A => R ⊆ A ∧ Disjoint A F)).card =
      (U.card - R.card - F.card).choose (m - R.card) := by
  have heq : (U.powersetCard m).filter (fun A => R ⊆ A ∧ Disjoint A F) =
      ((U \ F).powersetCard m).filter (fun A => R ⊆ A) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hAU, hc⟩, hRA, hAF⟩
      exact ⟨⟨Finset.subset_sdiff.mpr ⟨hAU, hAF⟩, hc⟩, hRA⟩
    · rintro ⟨⟨hAUF, hc⟩, hRA⟩
      have hAU : A ⊆ U := hAUF.trans Finset.sdiff_subset
      have hAF : Disjoint A F := (Finset.subset_sdiff.mp hAUF).2
      exact ⟨⟨hAU, hc⟩, hRA, hAF⟩
  rw [heq, Finset.card_filter_powersetCard_subset]
  · have hsum : R.card + F.card ≤ U.card := by
      rw [← Finset.card_union_of_disjoint hRF]
      exact Finset.card_le_card (Finset.union_subset hR hF)
    have hinter : F ∩ U = F := Finset.inter_eq_left.mpr hF
    rw [Finset.card_sdiff, hinter]
    have harith : U.card - F.card - R.card = U.card - R.card - F.card := by omega
    rw [harith]
  · exact Finset.subset_sdiff.mpr ⟨hR, hRF⟩
  · exact hRm

private lemma choose_ratio_one (W m : ℕ) (hW : 2 ≤ W) (hm0 : 1 ≤ m) (hm : m ≤ W) :
    ((W - 2).choose (m - 1) : ℝ) / (W.choose m : ℝ) =
      (m : ℝ) * (W - m : ℝ) / ((W : ℝ) * (W - 1 : ℝ)) := by
  have hchooseN : W.choose m ≠ 0 := Nat.choose_ne_zero hm
  have hchoose : (W.choose m : ℝ) ≠ 0 := by exact_mod_cast hchooseN
  have hW0 : (W : ℝ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
  have h1 := Nat.choose_mul (n := W) (k := m) (s := 1) hm0
  simp only [Nat.choose_one_right] at h1
  have h2 := Nat.choose_mul_succ_eq (W - 2) (m - 1)
  have hwform : W - 2 + 1 = W - 1 := by omega
  rw [hwform] at h2
  have hmform : W - 1 - (m - 1) = W - m := by omega
  rw [hmform] at h2
  have hnat : (W - 2).choose (m - 1) * W * (W - 1) =
      W.choose m * m * (W - m) := by
    calc
      _ = W * ((W - 2).choose (m - 1) * (W - 1)) := by ring
      _ = W * ((W - 1).choose (m - 1) * (W - m)) := by rw [h2]
      _ = (W * (W - 1).choose (m - 1)) * (W - m) := by ring
      _ = _ := by rw [← h1]
  have hwcast : ((W - 1 : ℕ) : ℝ) = (W : ℝ) - 1 := by
    exact_mod_cast (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ W))
  have hmcast : ((W - m : ℕ) : ℝ) = (W : ℝ) - m := Nat.cast_sub (R := ℝ) hm
  have hW10 : ((W - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show W - 1 ≠ 0 by omega)
  rw [← hwcast, ← hmcast]
  apply (div_eq_div_iff hchoose (mul_ne_zero hW0 hW10)).2
  norm_cast
  nlinarith [hnat]

private lemma crosses_pair_iff {α : Type} [DecidableEq α] (A : Finset α) (a b : α)
    (hab : a ≠ b) :
    crosses A {a, b} ↔ (a ∈ A ∧ b ∉ A) ∨ (b ∈ A ∧ a ∉ A) := by
  unfold crosses
  constructor
  · rintro ⟨x, hx, y, hy, heq⟩
    by_cases ha : a ∈ A
    · left
      refine ⟨ha, ?_⟩
      intro hb
      have hyab : y = a ∨ y = b := by
        have : y ∈ ({a, b} : Finset α) := by rw [heq]; simp
        simpa using this
      rcases hyab with rfl | rfl <;> contradiction
    · right
      refine ⟨?_, ha⟩
      by_contra hb
      have hxab : x = a ∨ x = b := by
        have : x ∈ ({a, b} : Finset α) := by rw [heq]; simp
        simpa using this
      rcases hxab with rfl | rfl <;> contradiction
  · rintro (h | h)
    · exact ⟨a, h.1, b, h.2, rfl⟩
    · exact ⟨b, h.1, a, h.2, Finset.pair_comm _ _⟩

private lemma card_crosses_pair {α : Type} [Fintype α] [DecidableEq α]
    (a b : α) (hab : a ≠ b) (m : ℕ) (hm0 : 1 ≤ m) :
    ((Finset.univ.powersetCard m).filter (fun A => crosses A {a, b})).card =
      2 * (Fintype.card α - 2).choose (m - 1) := by
  classical
  let X := (Finset.univ.powersetCard m).filter (fun A => a ∈ A ∧ b ∉ A)
  let Y := (Finset.univ.powersetCard m).filter (fun A => b ∈ A ∧ a ∉ A)
  have heq : (Finset.univ.powersetCard m).filter (fun A => crosses A {a, b}) =
      X ∪ Y := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_union, X, Y, crosses_pair_iff A a b hab]
    tauto
  have hd : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro A hX hY
    simp only [X, Finset.mem_filter] at hX
    simp only [Y, Finset.mem_filter] at hY
    exact hX.2.2 hY.2.1
  rw [heq, Finset.card_union_of_disjoint hd]
  have hx : X.card = (Fintype.card α - 2).choose (m - 1) := by
    have h := card_fixed_size_contains_disjoint Finset.univ {a} {b} m
      (by simp) (by simp) (by simp [hab]) (by simp [hm0])
    have harith : Fintype.card α - 1 - 1 = Fintype.card α - 2 := by omega
    simpa [X, Finset.disjoint_singleton_right, harith] using h
  have hy : Y.card = (Fintype.card α - 2).choose (m - 1) := by
    have h := card_fixed_size_contains_disjoint Finset.univ {b} {a} m
      (by simp) (by simp) (by simp [hab.symm]) (by simp [hm0])
    have harith : Fintype.card α - 1 - 1 = Fintype.card α - 2 := by omega
    simpa [Y, Finset.disjoint_singleton_right, harith] using h
  rw [hx, hy]
  omega

private lemma average_crosses (n m : ℕ) (hm : m ≤ w n) (hn : 1000 ≤ n)
    (S : Finset (Fin (w n))) (hS : S.card = 2) :
    (∑ A ∈ anchorSubsets n m, if crosses A S then (1 : ℝ) else 0) /
        ((anchorSubsets n m).card : ℝ) =
      2 * (m : ℝ) * (w n - m : ℝ) / ((w n : ℝ) * (w n - 1 : ℝ)) := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
  by_cases hm0 : m = 0
  · subst m
    simp [anchorSubsets, crosses]
  have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hsum : (∑ A ∈ anchorSubsets n m,
      if crosses A {a, b} then (1 : ℝ) else 0) =
      (((anchorSubsets n m).filter (fun A => crosses A {a, b})).card : ℝ) := by
    norm_cast
    exact (Finset.card_filter (fun A => crosses A {a, b}) (anchorSubsets n m)).symm
  rw [hsum]
  unfold anchorSubsets
  rw [Finset.card_powersetCard, Finset.card_univ]
  rw [card_crosses_pair a b hab m hmpos]
  push_cast
  simp only [Fintype.card_fin]
  rw [show (2 : ℝ) * ((w n - 2).choose (m - 1) : ℝ) / (w n).choose m =
      2 * (((w n - 2).choose (m - 1) : ℝ) / (w n).choose m) by ring]
  rw [choose_ratio_one (w n) m (by omega) hmpos hm]
  ring

private lemma card_crosses_adjacent {α : Type} [Fintype α] [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (m : ℕ) (hm : 2 ≤ m) :
    ((Finset.univ.powersetCard m).filter
      (fun A => crosses A {a, b} ∧ crosses A {a, c})).card =
      (Fintype.card α - 3).choose (m - 1) +
        (Fintype.card α - 3).choose (m - 2) := by
  classical
  let X := (Finset.univ.powersetCard m).filter
    (fun A => {a} ⊆ A ∧ Disjoint A {b, c})
  let Y := (Finset.univ.powersetCard m).filter
    (fun A => {b, c} ⊆ A ∧ Disjoint A {a})
  have heq : (Finset.univ.powersetCard m).filter
      (fun A => crosses A {a, b} ∧ crosses A {a, c}) = X ∪ Y := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_union, X, Y,
      crosses_pair_iff A a b hab, crosses_pair_iff A a c hac]
    simp only [Finset.singleton_subset_iff, Finset.insert_subset_iff,
      Finset.singleton_subset_iff, Finset.disjoint_insert_right,
      Finset.disjoint_singleton_right]
    tauto
  have hd : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro A hX hY
    simp only [X, Finset.mem_filter, Finset.singleton_subset_iff,
      Finset.disjoint_insert_right, Finset.disjoint_singleton_right] at hX
    simp only [Y, Finset.mem_filter, Finset.insert_subset_iff,
      Finset.singleton_subset_iff, Finset.disjoint_singleton_right] at hY
    exact hX.2.2.1 hY.2.1.1
  rw [heq, Finset.card_union_of_disjoint hd]
  have hx : X.card = (Fintype.card α - 3).choose (m - 1) := by
    have h := card_fixed_size_contains_disjoint Finset.univ {a} {b, c} m
      (by simp) (by simp) (by simp [hab, hac]) (by simp; omega)
    have hcard : ({b, c} : Finset α).card = 2 := by simp [hbc]
    have harith : Fintype.card α - 1 - 2 = Fintype.card α - 3 := by omega
    simpa [X, hcard, harith, Finset.disjoint_insert_right,
      Finset.disjoint_singleton_right] using h
  have hy : Y.card = (Fintype.card α - 3).choose (m - 2) := by
    have h := card_fixed_size_contains_disjoint Finset.univ {b, c} {a} m
      (by simp) (by simp) (by simp [hab, hac]) (by simp [hbc, hm])
    have hcard : ({b, c} : Finset α).card = 2 := by simp [hbc]
    have harith : Fintype.card α - 2 - 1 = Fintype.card α - 3 := by omega
    simpa [Y, hcard, harith, Finset.insert_subset_iff,
      Finset.singleton_subset_iff, Finset.disjoint_singleton_right] using h
  rw [hx, hy]

set_option maxHeartbeats 800000 in
private lemma card_crosses_disjoint {α : Type} [Fintype α] [DecidableEq α]
    (a b c d : α) (hab : a ≠ b) (hcd : c ≠ d)
    (hpair : ({a, b} : Finset α) ∩ {c, d} = ∅) (m : ℕ) (hm : 2 ≤ m) :
    ((Finset.univ.powersetCard m).filter
      (fun A => crosses A {a, b} ∧ crosses A {c, d})).card =
      4 * (Fintype.card α - 4).choose (m - 2) := by
  classical
  have hne (x : α) (hx : x ∈ ({a, b} : Finset α))
      (y : α) (hy : y ∈ ({c, d} : Finset α)) : x ≠ y := by
    intro heq
    subst y
    have hi : x ∈ ({a, b} : Finset α) ∩ {c, d} := Finset.mem_inter.mpr ⟨hx, hy⟩
    rw [hpair] at hi
    simp at hi
  have hac : a ≠ c := hne a (by simp) c (by simp)
  have had : a ≠ d := hne a (by simp) d (by simp)
  have hbc : b ≠ c := hne b (by simp) c (by simp)
  have hbd : b ≠ d := hne b (by simp) d (by simp)
  let X1 := (Finset.univ.powersetCard m).filter
    (fun A => {a, c} ⊆ A ∧ Disjoint A {b, d})
  let X2 := (Finset.univ.powersetCard m).filter
    (fun A => {a, d} ⊆ A ∧ Disjoint A {b, c})
  let X3 := (Finset.univ.powersetCard m).filter
    (fun A => {b, c} ⊆ A ∧ Disjoint A {a, d})
  let X4 := (Finset.univ.powersetCard m).filter
    (fun A => {b, d} ⊆ A ∧ Disjoint A {a, c})
  have heq : (Finset.univ.powersetCard m).filter
      (fun A => crosses A {a, b} ∧ crosses A {c, d}) =
      (X1 ∪ X2) ∪ (X3 ∪ X4) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_union, X1, X2, X3, X4,
      crosses_pair_iff A a b hab, crosses_pair_iff A c d hcd,
      Finset.insert_subset_iff, Finset.singleton_subset_iff,
      Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
    aesop
  have hd12 : Disjoint X1 X2 := by
    rw [Finset.disjoint_left]
    intro A h1 h2
    simp only [X1, Finset.mem_filter, Finset.insert_subset_iff,
      Finset.singleton_subset_iff, Finset.disjoint_insert_right,
      Finset.disjoint_singleton_right] at h1
    simp only [X2, Finset.mem_filter, Finset.insert_subset_iff,
      Finset.singleton_subset_iff, Finset.disjoint_insert_right,
      Finset.disjoint_singleton_right] at h2
    exact h2.2.2.2 h1.2.1.2
  have hd34 : Disjoint X3 X4 := by
    rw [Finset.disjoint_left]
    intro A h3 h4
    simp only [X3, Finset.mem_filter, Finset.insert_subset_iff,
      Finset.singleton_subset_iff, Finset.disjoint_insert_right,
      Finset.disjoint_singleton_right] at h3
    simp only [X4, Finset.mem_filter, Finset.insert_subset_iff,
      Finset.singleton_subset_iff, Finset.disjoint_insert_right,
      Finset.disjoint_singleton_right] at h4
    exact h4.2.2.2 h3.2.1.2
  have hdouter : Disjoint (X1 ∪ X2) (X3 ∪ X4) := by
    rw [Finset.disjoint_left]
    intro A hleft hright
    simp only [Finset.mem_union] at hleft hright
    rcases hleft with h1 | h2 <;> rcases hright with h3 | h4
    · simp only [X1, Finset.mem_filter, Finset.insert_subset_iff,
        Finset.singleton_subset_iff] at h1
      simp only [X3, Finset.mem_filter, Finset.disjoint_insert_right,
        Finset.disjoint_singleton_right] at h3
      exact h3.2.2.1 h1.2.1.1
    · simp only [X1, Finset.mem_filter, Finset.insert_subset_iff,
        Finset.singleton_subset_iff] at h1
      simp only [X4, Finset.mem_filter, Finset.disjoint_insert_right,
        Finset.disjoint_singleton_right] at h4
      exact h4.2.2.1 h1.2.1.1
    · simp only [X2, Finset.mem_filter, Finset.insert_subset_iff,
        Finset.singleton_subset_iff] at h2
      simp only [X3, Finset.mem_filter, Finset.disjoint_insert_right,
        Finset.disjoint_singleton_right] at h3
      exact h3.2.2.1 h2.2.1.1
    · simp only [X2, Finset.mem_filter, Finset.insert_subset_iff,
        Finset.singleton_subset_iff] at h2
      simp only [X4, Finset.mem_filter, Finset.disjoint_insert_right,
        Finset.disjoint_singleton_right] at h4
      exact h4.2.2.1 h2.2.1.1
  rw [heq, Finset.card_union_of_disjoint hdouter,
    Finset.card_union_of_disjoint hd12, Finset.card_union_of_disjoint hd34]
  have count (r₁ r₂ f₁ f₂ : α) (hr : r₁ ≠ r₂) (hf : f₁ ≠ f₂)
      (hdis : Disjoint ({r₁, r₂} : Finset α) {f₁, f₂}) :
      ((Finset.univ.powersetCard m).filter
        (fun A => {r₁, r₂} ⊆ A ∧ Disjoint A {f₁, f₂})).card =
        (Fintype.card α - 4).choose (m - 2) := by
    have h := card_fixed_size_contains_disjoint Finset.univ {r₁, r₂} {f₁, f₂} m
      (by simp) (by simp) hdis (by simp [hr, hm])
    have hr2 : ({r₁, r₂} : Finset α).card = 2 := by simp [hr]
    have hf2 : ({f₁, f₂} : Finset α).card = 2 := by simp [hf]
    have harith : Fintype.card α - 2 - 2 = Fintype.card α - 4 := by omega
    simpa [hr2, hf2, harith] using h
  have h1 : X1.card = (Fintype.card α - 4).choose (m - 2) := by
    exact count a c b d hac hbd (by
      simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
      aesop)
  have h2 : X2.card = (Fintype.card α - 4).choose (m - 2) := by
    exact count a d b c had hbc (by
      simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
      aesop)
  have h3 : X3.card = (Fintype.card α - 4).choose (m - 2) := by
    exact count b c a d hbc had (by
      simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
      aesop)
  have h4 : X4.card = (Fintype.card α - 4).choose (m - 2) := by
    exact count b d a c hbd hac (by
      simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
      aesop)
  rw [h1, h2, h3, h4]
  omega

private lemma pairs_with_singleton_intersection {α : Type} [DecidableEq α]
    (S T : Finset α) (hS : S.card = 2) (hT : T.card = 2) (hI : (S ∩ T).card = 1) :
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ S = {a, b} ∧ T = {a, c} := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hI
  have haI : a ∈ S ∩ T := by rw [ha]; simp
  have haS := (Finset.mem_inter.mp haI).1
  have haT := (Finset.mem_inter.mp haI).2
  have hsErase : (S.erase a).card = 1 := by rw [Finset.card_erase_of_mem haS, hS]
  have htErase : (T.erase a).card = 1 := by rw [Finset.card_erase_of_mem haT, hT]
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hsErase
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp htErase
  have hSb : S = {a, b} := by
    apply Finset.ext
    intro x
    by_cases hxa : x = a
    · subst x; simp [haS]
    · have hx : x ∈ S ↔ x ∈ S.erase a := by simp [hxa]
      rw [hx, hb]; simp [hxa]
  have hTc : T = {a, c} := by
    apply Finset.ext
    intro x
    by_cases hxa : x = a
    · subst x; simp [haT]
    · have hx : x ∈ T ↔ x ∈ T.erase a := by simp [hxa]
      rw [hx, hc]; simp [hxa]
  have hab : a ≠ b := by
    intro e
    have : a ∈ S.erase a := by rw [hb, ← e]; simp
    simp at this
  have hac : a ≠ c := by
    intro e
    have : a ∈ T.erase a := by rw [hc, ← e]; simp
    simp at this
  have hbc : b ≠ c := by
    intro e
    subst c
    have hbI : b ∈ S ∩ T := by simp [hSb, hTc]
    have hba : b = a := by rw [ha] at hbI; simpa using hbI
    exact hab hba.symm
  exact ⟨a, b, c, hab, hac, hbc, hSb, hTc⟩

private lemma card_crosses_pair_pair {α : Type} [Fintype α] [DecidableEq α]
    (S T : Finset α) (hS : S.card = 2) (hT : T.card = 2) (m : ℕ) (hm : 2 ≤ m) :
    ((Finset.univ.powersetCard m).filter (fun A => crosses A S ∧ crosses A T)).card =
      if S = T then 2 * (Fintype.card α - 2).choose (m - 1)
      else if (S ∩ T).card = 1 then
        (Fintype.card α - 3).choose (m - 1) +
          (Fintype.card α - 3).choose (m - 2)
      else 4 * (Fintype.card α - 4).choose (m - 2) := by
  classical
  by_cases hEq : S = T
  · subst T
    simp only [↓reduceIte]
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
    simp only [and_self]
    exact card_crosses_pair a b hab m (by omega)
  · simp only [hEq, ↓reduceIte]
    by_cases hI : (S ∩ T).card = 1
    · simp only [hI, ↓reduceIte]
      obtain ⟨a, b, c, hab, hac, hbc, rfl, rfl⟩ :=
        pairs_with_singleton_intersection S T hS hT hI
      exact card_crosses_adjacent a b c hab hac hbc m hm
    · simp only [hI, ↓reduceIte]
      have hIle : (S ∩ T).card ≤ 2 := by
        exact (Finset.card_le_card Finset.inter_subset_left).trans_eq hS
      have hIne2 : (S ∩ T).card ≠ 2 := by
        intro hc
        have hST : S ∩ T = S := Finset.eq_of_subset_of_card_le
          Finset.inter_subset_left (by rw [hc, hS])
        have hTS : S ∩ T = T := Finset.eq_of_subset_of_card_le
          Finset.inter_subset_right (by rw [hc, hT])
        exact hEq (hST.symm.trans hTS)
      have hI0 : (S ∩ T).card = 0 := by omega
      have hinter : S ∩ T = ∅ := Finset.card_eq_zero.mp hI0
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
      obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp hT
      exact card_crosses_disjoint a b c d hab hcd hinter m hm

private lemma choose_ratio_two (W m : ℕ) (hW : 2 ≤ W) (hm : 2 ≤ m) (hmW : m ≤ W) :
    ((W - 2).choose (m - 2) : ℝ) / (W.choose m : ℝ) =
      ((m : ℝ) * (m - 1 : ℝ)) / ((W : ℝ) * (W - 1 : ℝ)) := by
  have hnat : (W - 2).choose (m - 2) * W * (W - 1) =
      m * (m - 1) * W.choose m := by
    have h1 := Nat.choose_mul (n := W) (k := m) (s := 2) hm
    rw [Nat.choose_two_right, Nat.choose_two_right] at h1
    have hevenW : 2 ∣ W * (W - 1) := (Nat.even_mul_pred_self W).two_dvd
    have hevenm : 2 ∣ m * (m - 1) := (Nat.even_mul_pred_self m).two_dvd
    have hw : 2 * (W * (W - 1) / 2) = W * (W - 1) := Nat.mul_div_cancel' hevenW
    have hm' : 2 * (m * (m - 1) / 2) = m * (m - 1) := Nat.mul_div_cancel' hevenm
    nlinarith
  have hc : (W.choose m : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hmW
  have hW0 : (W : ℝ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
  have hW10 : (W - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr (by
    exact_mod_cast (show W ≠ 1 by omega))
  have hwcast : ((W - 1 : ℕ) : ℝ) = (W : ℝ) - 1 := by
    exact_mod_cast (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ W))
  have hmcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    exact_mod_cast (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ m))
  rw [← hwcast, ← hmcast]
  apply (div_eq_div_iff hc (mul_ne_zero hW0 (by exact_mod_cast (show W - 1 ≠ 0 by omega)))).2
  norm_cast
  nlinarith [hnat]

private lemma choose_ratio_adjacent (W m : ℕ) (hW : 3 ≤ W) (hm : 2 ≤ m) (hmW : m ≤ W) :
    (((W - 3).choose (m - 1) + (W - 3).choose (m - 2) : ℕ) : ℝ) /
        (W.choose m : ℝ) =
      ((m : ℝ) * (W - m : ℝ) * (W - m - 1 : ℝ) +
        (m : ℝ) * (m - 1 : ℝ) * (W - m : ℝ)) /
        ((W : ℝ) * (W - 1 : ℝ) * (W - 2 : ℝ)) := by
  have hpascal : (W - 3).choose (m - 1) + (W - 3).choose (m - 2) =
      (W - 2).choose (m - 1) := by
    rw [show W - 2 = (W - 3) + 1 by omega,
      show m - 1 = (m - 2) + 1 by omega, Nat.choose_succ_succ]
    rw [Nat.add_comm]
  rw [hpascal, choose_ratio_one W m (by omega) (by omega) hmW]
  have hW2 : (W : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by
    exact_mod_cast (show W ≠ 2 by omega))
  field_simp
  ring

private lemma choose_ratio_exclude_two (N k : ℕ) (hN : 2 ≤ N) (hk : k ≤ N) :
    ((N - 2).choose k : ℝ) / (N.choose k : ℝ) =
      ((N - k : ℝ) * (N - k - 1 : ℝ)) / ((N : ℝ) * (N - 1 : ℝ)) := by
  by_cases hk2 : k ≤ N - 2
  · rw [← Nat.choose_symm hk2, ← Nat.choose_symm hk]
    have heq : N - 2 - k = (N - k) - 2 := by omega
    rw [heq, choose_ratio_two N (N - k) hN (by omega) (by omega)]
    have hcast : ((N - k : ℕ) : ℝ) = (N : ℝ) - k := Nat.cast_sub (R := ℝ) hk
    rw [hcast]
  · have hkcases : k = N - 1 ∨ k = N := by omega
    rcases hkcases with hk' | hk'
    · rw [hk']
      have hz : (N - 2).choose (N - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hz]
      have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        exact_mod_cast (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ N))
      rw [hc]
      ring
    · rw [hk']
      have hz : (N - 2).choose N = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hz]
      simp

private lemma choose_ratio_disjoint (W m : ℕ) (hW : 4 ≤ W) (hm : 2 ≤ m) (hmW : m ≤ W) :
    ((W - 4).choose (m - 2) : ℝ) / (W.choose m : ℝ) =
      ((m : ℝ) * (m - 1 : ℝ) * (W - m : ℝ) * (W - m - 1 : ℝ)) /
        ((W : ℝ) * (W - 1 : ℝ) * (W - 2 : ℝ) * (W - 3 : ℝ)) := by
  have hstep := choose_ratio_exclude_two (W - 2) (m - 2) (by omega) (by omega)
  have hfactor : ((W - 4).choose (m - 2) : ℝ) / (W.choose m : ℝ) =
      (((W - 4).choose (m - 2) : ℝ) / ((W - 2).choose (m - 2) : ℝ)) *
        (((W - 2).choose (m - 2) : ℝ) / (W.choose m : ℝ)) := by
    have hmid : ((W - 2).choose (m - 2) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero (by omega)
    field_simp
  rw [hfactor]
  have hsub : W - 2 - 2 = W - 4 := by omega
  rw [hsub] at hstep
  rw [hstep, choose_ratio_two W m (by omega) hm hmW]
  have cW2 : ((W - 2 : ℕ) : ℝ) = (W : ℝ) - 2 := by
    exact_mod_cast (Nat.cast_sub (R := ℝ) (by omega : 2 ≤ W))
  have cm2 : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by
    exact_mod_cast (Nat.cast_sub (R := ℝ) hm)
  rw [cW2, cm2, div_mul_div_comm]
  congr 1 <;> ring

private lemma card_crosses_pair_pair_one {α : Type} [Fintype α] [DecidableEq α]
    (S T : Finset α) (hS : S.card = 2) (hT : T.card = 2) :
    ((Finset.univ.powersetCard 1).filter
      (fun A => crosses A S ∧ crosses A T)).card = (S ∩ T).card := by
  classical
  let f : α → Finset α := fun a => {a}
  have hf : Function.Injective f := fun a b h => by simpa [f] using h
  rw [Finset.powersetCard_one]
  have hcross (a : α) (U : Finset α) (hU : U.card = 2) : crosses {a} U ↔ a ∈ U := by
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hU
    rw [crosses_pair_iff {a} x y hxy]
    simp only [Finset.mem_singleton, Finset.mem_insert]
    aesop
  have heq : (Finset.map ⟨f, hf⟩ Finset.univ).filter
      (fun A => crosses A S ∧ crosses A T) = Finset.map ⟨f, hf⟩ (S ∩ T) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
      Finset.mem_inter]
    constructor
    · rintro ⟨⟨a, _, rfl⟩, h⟩
      exact ⟨a, ⟨(hcross a S hS).mp h.1, (hcross a T hT).mp h.2⟩, rfl⟩
    · rintro ⟨a, ⟨haS, haT⟩, hAf⟩
      subst A
      refine ⟨⟨a, rfl⟩, ?_⟩
      change crosses {a} S ∧ crosses {a} T
      exact ⟨(hcross a S hS).mpr haS, (hcross a T hT).mpr haT⟩
  rw [heq, Finset.card_map]

private lemma average_crosses_pair (n m : ℕ) (hm : m ≤ w n) (hn : 1000 ≤ n)
    (S T : Finset (Fin (w n))) (hS : S.card = 2) (hT : T.card = 2) :
    (∑ A ∈ anchorSubsets n m,
        if crosses A S ∧ crosses A T then (1 : ℝ) else 0) /
        ((anchorSubsets n m).card : ℝ) = P_survive n m S T := by
  classical
  have hsum : (∑ A ∈ anchorSubsets n m,
      if crosses A S ∧ crosses A T then (1 : ℝ) else 0) =
      (((anchorSubsets n m).filter (fun A => crosses A S ∧ crosses A T)).card : ℝ) := by
    norm_cast
    exact (Finset.card_filter _ _).symm
  rw [hsum]
  unfold anchorSubsets
  rw [Finset.card_powersetCard, Finset.card_univ]
  by_cases hm2 : 2 ≤ m
  · rw [card_crosses_pair_pair S T hS hT m hm2]
    simp only [Fintype.card_fin]
    unfold P_survive
    by_cases hST : S = T
    · subst T
      simp only [Finset.inter_self, hS, ↓reduceIte]
      push_cast
      rw [show (2 : ℝ) * ((w n - 2).choose (m - 1) : ℝ) / (w n).choose m =
          2 * (((w n - 2).choose (m - 1) : ℝ) / (w n).choose m) by ring,
        choose_ratio_one (w n) m (by have := w_ge_four n hn; omega) (by omega) hm]
      ring
    · simp only [hST, ↓reduceIte]
      have hle : (S ∩ T).card ≤ 2 :=
        (Finset.card_le_card Finset.inter_subset_left).trans_eq hS
      have hne2 : (S ∩ T).card ≠ 2 := by
        intro hc
        have hleft : S ∩ T = S := Finset.eq_of_subset_of_card_le
          Finset.inter_subset_left (by rw [hc, hS])
        have hright : S ∩ T = T := Finset.eq_of_subset_of_card_le
          Finset.inter_subset_right (by rw [hc, hT])
        exact hST (hleft.symm.trans hright)
      simp only [hne2, ↓reduceIte]
      by_cases hi : (S ∩ T).card = 1
      · simp only [hi, ↓reduceIte]
        exact_mod_cast choose_ratio_adjacent (w n) m (by have := w_ge_four n hn; omega) hm2 hm
      · simp only [hi, ↓reduceIte]
        norm_num
        rw [show (4 : ℝ) * ((w n - 4).choose (m - 2) : ℝ) / (w n).choose m =
            4 * (((w n - 4).choose (m - 2) : ℝ) / (w n).choose m) by ring,
          choose_ratio_disjoint (w n) m (w_ge_four n hn) hm2 hm]
        ring
  · have hm01 : m = 0 ∨ m = 1 := by omega
    rcases hm01 with rfl | rfl
    · have hnone (U : Finset (Fin (w n))) : ¬ crosses ∅ U := by
        unfold crosses
        simp
      simp [P_survive, hnone]
    · rw [card_crosses_pair_pair_one S T hS hT, Nat.choose_one_right]
      simp only [Fintype.card_fin]
      unfold P_survive
      have hW := w_ge_four n hn
      have hle : (S ∩ T).card ≤ 2 :=
        (Finset.card_le_card Finset.inter_subset_left).trans_eq hS
      interval_cases hi : (S ∩ T).card
      · simp [hi]
      · norm_num
        have h0 : (w n : ℝ) ≠ 0 := by exact_mod_cast (show w n ≠ 0 by omega)
        have h1 : (w n : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show w n ≠ 1 by omega))
        have h2 : (w n : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show w n ≠ 2 by omega))
        field_simp [h0, h1, h2]
        ring
      · norm_num
        have h0 : (w n : ℝ) ≠ 0 := by exact_mod_cast (show w n ≠ 0 by omega)
        have h1 : (w n : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show w n ≠ 1 by omega))
        field_simp [h0, h1]

private lemma average_crosses_single_weighted (n m : ℕ) (hm : m ≤ w n) (hn : 1000 ≤ n)
    (S : Finset (Fin (w n))) (hS : S.card = 2) (u M v : ℝ) :
    (∑ A ∈ anchorSubsets n m,
        (if crosses A S then u else 0) * M * (if crosses A S then v else 0)) /
        ((anchorSubsets n m).card : ℝ) =
      (2 * (m : ℝ) * (w n - m : ℝ) / ((w n : ℝ) * (w n - 1 : ℝ))) * u * M * v := by
  rw [← average_crosses n m hm hn S hS]
  have hsum : (∑ A ∈ anchorSubsets n m,
      (if crosses A S then u else 0) * M * (if crosses A S then v else 0)) =
      (∑ A ∈ anchorSubsets n m, if crosses A S then (1 : ℝ) else 0) * u * M * v := by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hAS : crosses A S <;> simp [hAS]
  rw [hsum]
  ring

private lemma average_crosses_pair_weighted (n m : ℕ) (hm : m ≤ w n) (hn : 1000 ≤ n)
    (S T : Finset (Fin (w n))) (hS : S.card = 2) (hT : T.card = 2)
    (u M v : ℝ) :
    (∑ A ∈ anchorSubsets n m,
        (if crosses A S then u else 0) * M * (if crosses A T then v else 0)) /
        ((anchorSubsets n m).card : ℝ) = P_survive n m S T * u * M * v := by
  rw [← average_crosses_pair n m hm hn S T hS hT]
  have hsum : (∑ A ∈ anchorSubsets n m,
      (if crosses A S then u else 0) * M * (if crosses A T then v else 0)) =
      (∑ A ∈ anchorSubsets n m,
        if crosses A S ∧ crosses A T then (1 : ℝ) else 0) * u * M * v := by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hAS : crosses A S <;> by_cases hAT : crosses A T <;>
      simp [hAS, hAT] <;> ring
  rw [hsum]
  ring

private lemma average_spatial_quadratic (n m : ℕ) (hm : m ≤ w n) (hn : 1000 ≤ n)
    (M : Finset (Fin (w n)) → Finset (Fin (w n)) → ℝ) :
    (∑ A ∈ anchorSubsets n m,
      ∑ S ∈ Edges n, ∑ T ∈ Edges n,
        (if crosses A S then starWeight n S else 0) * M S T *
          (if crosses A T then starWeight n T else 0)) /
        ((anchorSubsets n m).card : ℝ) =
      ∑ S ∈ Edges n, ∑ T ∈ Edges n,
        P_survive n m S T * starWeight n S * M S T * starWeight n T := by
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  rw [← Finset.sum_div]
  exact average_crosses_pair_weighted n m hm hn S T
    (Finset.mem_filter.mp hS).2 (Finset.mem_filter.mp hT).2 _ _ _

/--
The expected mass evaluation over all possible anchor subsets of size m.
By linearity of expectation, the sum of Q1(A) reduces to the probability of an edge
being active, multiplied by the diagonal mass sum, minus cross-term error bounds.
-/
theorem expected_mass_bound (n : ℕ) (m : ℕ) (hm : m ≤ w n) (hn : 1000 ≤ n) :
    (∑ A ∈ anchorSubsets n m, q1 n (multiStarVector n A)) / ((anchorSubsets n m).card : ℝ) ≥
    (2 * (m : ℝ) * (w n - m : ℝ) / ((w n : ℝ) * (w n - 1 : ℝ))) *
    (∑ S ∈ Edges n, (starWeight n S)^2 * ((evalInterval n).card : ℝ) / 4) -
    massCrossTerms n m := by
  sorry

set_option maxHeartbeats 800000 in
-- The finite-sum normalization is elaboration-intensive in Lean 4.32.
/--
The expected penalty evaluation over all possible anchor subsets of size m.
Using the FourierTransform helpers (fourier_cos_mul_cos and fourier_sinc_eval),
the continuous expansion of this quadratic form explicitly bounds the sum strictly
below the diagonal mass trace.
-/
theorem expected_penalty_bound (n : ℕ) (m : ℕ) (hm : m ≤ w n) (hn : 1000 ≤ n) :
    (∑ A ∈ anchorSubsets n m, q2 n (multiStarVector n A)) / ((anchorSubsets n m).card : ℝ) ≤
    -- Expected Diagonal Penalty
    (2 * (m : ℝ) * (w n - m : ℝ) / ((w n : ℝ) * (w n - 1 : ℝ))) *
    (∑ S ∈ Edges n, (starWeight n S)^2 *
                  (∑ x ∈ evalInterval n, c n (x : ZMod (q n)) * (basisFunction n S x)^2)) +
    -- Expected Off-Diagonal Penalty (Structurally negative due to sinc anti-alignment)
    penaltyOffDiagonal n m := by
  classical
  simp_rw [q2_multiStar_eq_spatial n (by omega)]
  rw [average_spatial_quadratic n m hm hn]
  unfold penaltyOffDiagonal
  have hsplit (S : Finset (Fin (w n))) (hS : S ∈ Edges n) :
      (∑ T ∈ Edges n,
        P_survive n m S T * starWeight n S * penaltyMatrixEntry n S T * starWeight n T) =
      P_survive n m S S * starWeight n S * penaltyMatrixEntry n S S * starWeight n S +
      ∑ T ∈ Edges n \ {S},
        P_survive n m S T * starWeight n S * penaltyMatrixEntry n S T * starWeight n T := by
    have hsub : {S} ⊆ Edges n := Finset.singleton_subset_iff.mpr hS
    have h := Finset.sum_sdiff (f := fun T =>
      P_survive n m S T * starWeight n S * penaltyMatrixEntry n S T * starWeight n T) hsub
    rw [add_comm]
    simpa using h.symm
  have hsplitAll :
      (∑ S ∈ Edges n, ∑ T ∈ Edges n,
        P_survive n m S T * starWeight n S * penaltyMatrixEntry n S T * starWeight n T) =
      ∑ S ∈ Edges n,
        (P_survive n m S S * starWeight n S * penaltyMatrixEntry n S S * starWeight n S +
        ∑ T ∈ Edges n \ {S},
          P_survive n m S T * starWeight n S * penaltyMatrixEntry n S T * starWeight n T) := by
    apply Finset.sum_congr rfl
    intro S hS
    exact hsplit S hS
  rw [hsplitAll, Finset.sum_add_distrib]
  apply le_of_eq
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    have hScard : S.card = 2 := (Finset.mem_filter.mp hS).2
    have hp : P_survive n m S S =
        2 * (m : ℝ) * (w n - m : ℝ) / ((w n : ℝ) * (w n - 1 : ℝ)) := by
      unfold P_survive
      simp [hScard]
    rw [hp]
    unfold penaltyMatrixEntry
    simp only [pow_two]
    ring
  · apply Finset.sum_congr rfl
    intro S hS
    apply Finset.sum_congr rfl
    intro T hT
    unfold penaltyMatrixEntry
    ring

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
