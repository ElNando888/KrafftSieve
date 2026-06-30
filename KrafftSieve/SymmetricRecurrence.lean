/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gemini 3.5 Flash (Google DeepMind)
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Symmetric Polynomials and Vieta DP Recurrence

This file formalizes the elementary symmetric polynomials (Vieta's formulas)
and verifies their dynamic programming recurrence.
-/

namespace KrafftSieve

open scoped BigOperators

/--
The j-th elementary symmetric polynomial over a finite set s.
-/
def esymmSum {α : Type*} (j : ℕ) (s : Finset α) (f : α → ℝ) : ℝ :=
  ∑ t ∈ s.powersetCard j, ∏ i ∈ t, f i

/--
Theorem: The recurrence relation for elementary symmetric polynomials.
$$ e_{j+1}(s ∪ {x}) = e_{j+1}(s) + f(x) * e_j(s) $$
-/
theorem esymmSum_insert [DecidableEq α] {x : α} {s : Finset α} (h : x ∉ s) (j : ℕ) (f : α → ℝ) :
    esymmSum (j + 1) (insert x s) f = esymmSum (j + 1) s f + f x * esymmSum j s f := by
  unfold esymmSum
  rw [Finset.powersetCard_succ_insert h]
  have h_disj : Disjoint (s.powersetCard (j + 1)) ((s.powersetCard j).image (insert x)) := by
    rw [Finset.disjoint_left]
    rintro t1 ht1
    rw [Finset.mem_image]
    rintro ⟨t2, ht2, rfl⟩
    have h_in_s : x ∈ s := Finset.mem_powersetCard.mp ht1 |>.1 (Finset.mem_insert_self x t2)
    exact h h_in_s
  rw [Finset.sum_union h_disj]
  congr 1
  have h_inj : ∀ t1 ∈ s.powersetCard j, ∀ t2 ∈ s.powersetCard j,
      insert x t1 = insert x t2 → t1 = t2 := by
    intro t1 ht1 t2 ht2 h_eq
    have hxt1 : x ∉ t1 := fun h_in ↦ h (Finset.mem_powersetCard.mp ht1 |>.1 h_in)
    have hxt2 : x ∉ t2 := fun h_in ↦ h (Finset.mem_powersetCard.mp ht2 |>.1 h_in)
    have h1 : Finset.erase (insert x t1) x = t1 := Finset.erase_insert hxt1
    have h2 : Finset.erase (insert x t2) x = t2 := Finset.erase_insert hxt2
    rw [← h1, ← h2, h_eq]
  rw [Finset.sum_image h_inj]
  have h_prod : ∀ t ∈ s.powersetCard j, ∏ i ∈ insert x t, f i = f x * ∏ i ∈ t, f i := by
    intro t ht
    have hxt : x ∉ t := fun h_in ↦ h (Finset.mem_powersetCard.mp ht |>.1 h_in)
    exact Finset.prod_insert hxt
  have h_sum_congr : (∑ t ∈ s.powersetCard j, ∏ i ∈ insert x t, f i) =
      (∑ t ∈ s.powersetCard j, f x * ∏ i ∈ t, f i) := by
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    rw [h_prod t ht]
  rw [h_sum_congr, ← Finset.mul_sum]

/--
Recursive definition of the dynamic programming algorithm for computing symmetric polynomials.
-/
def dpRec (w : ℕ) (f : Fin w → ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | i + 1, j + 1 =>
    if h : i < w then
      dpRec w f i (j + 1) + f ⟨i, h⟩ * dpRec w f i j
    else
      0

/--
The prefix set containing the first i elements of Fin w.
-/
def prefixFin (w : ℕ) (i : ℕ) : Finset (Fin w) :=
  Finset.univ.filter (fun x ↦ x.val < i)

lemma prefixFin_zero (w : ℕ) : prefixFin w 0 = ∅ := by
  unfold prefixFin
  ext _
  simp

lemma prefixFin_succ (w : ℕ) (i : ℕ) (h : i < w) :
    prefixFin w (i + 1) = insert ⟨i, h⟩ (prefixFin w i) := by
  unfold prefixFin
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

lemma not_mem_prefixFin (w : ℕ) (i : ℕ) (h : i < w) :
    ⟨i, h⟩ ∉ prefixFin w i := by
  unfold prefixFin
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact lt_irrefl i

/--
Theorem: The recursive dynamic programming algorithm computes the
elementary symmetric polynomials correctly.
-/
theorem dpRec_eq_esymmSum (w : ℕ) (f : Fin w → ℝ) (i : ℕ) (j : ℕ)
    (hi : i ≤ w) :
    dpRec w f i j = esymmSum j (prefixFin w i) f := by
  induction i generalizing j with
  | zero =>
    rw [prefixFin_zero]
    rcases j with _|j
    · unfold dpRec esymmSum; simp
    · unfold dpRec esymmSum
      rw [Finset.powersetCard_eq_empty.mpr (by simp)]
      rw [Finset.sum_empty]
  | succ i ih =>
    have hi_lt : i < w := by omega
    have hi_le : i ≤ w := by omega
    rcases j with _|j
    · rw [prefixFin_succ w i hi_lt]
      unfold dpRec esymmSum; simp
    · rw [prefixFin_succ w i hi_lt]
      unfold dpRec
      rw [dif_pos hi_lt]
      rw [ih (j + 1) hi_le, ih j hi_le]
      rw [esymmSum_insert (not_mem_prefixFin w i hi_lt)]

end KrafftSieve
