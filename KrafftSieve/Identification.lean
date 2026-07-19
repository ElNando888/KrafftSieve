/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import KrafftSieve.RidgeGraph

/-!
# Identification Lemmas

This module provides explicit mathematical equivalences between the cyclic definitions
(over `ZMod (q n)`) and the integer interval definitions (over `evalInterval n`).
These lemmas are crucial for bounding the cyclic quadratic forms `q1` and `q2`
using properties of the Ridge Graph evaluated on the integer interval.
-/

namespace KrafftSieve

open scoped BigOperators Real

/-- The discrete basis cosines evaluated on elements of the evaluation interval
exactly match the continuous basis functions evaluated on integers. -/
lemma basisCos_eq_basisFunction (n : ℕ) (S : Finset (Fin (w n))) (x : ℕ) (hx : x ∈ evalInterval n)
    (hn : 1 ≤ n) :
    basisCos n S (x : ZMod (q n)) = basisFunction n S x := by
  have hxq : x < q n :=
    lt_of_le_of_lt (Finset.mem_Icc.mp hx).2 (q_bound n hn)
  have hval : ((x : ZMod (q n)).val = x) := ZMod.val_natCast_of_lt hxq
  unfold basisCos basisFunction
  rw [hval]
  congr 1
  funext i
  ring_nf

/-- The first moment matrix evaluated cyclically matches the mass matrix entry over the interval. -/
lemma matrix1_eq_massMatrixEntry (n : ℕ) (hn : 1 ≤ n) (S T : Finset (Fin (w n))) :
    matrix1 n S T = massMatrixEntry n S T := by
  have hsub : evalInterval n ⊆ Finset.range (q n) := by
    intro x hx
    exact Finset.mem_range.mpr
      (lt_of_le_of_lt (Finset.mem_Icc.mp hx).2 (q_bound n hn))
  unfold matrix1 massMatrixEntry
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hxq : x < q n := Finset.mem_range.mp (hsub hx)
    have hval : ((x : ZMod (q n)).val = x) := ZMod.val_natCast_of_lt hxq
    rw [basisCos_eq_basisFunction n S x hx hn,
      basisCos_eq_basisFunction n T x hx hn]
    simp [Psi, hval, hx]
  · intro x hx hx'
    have hval : ((x : ZMod (q n)).val = x) :=
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hx)
    simp [Psi, hval, hx']

/-- The second moment matrix evaluated cyclically matches the penalty matrix entry over the interval. -/
lemma matrix2_eq_penaltyMatrixEntry (n : ℕ) (hn : 1 ≤ n) (S T : Finset (Fin (w n))) :
    matrix2 n S T = penaltyMatrixEntry n S T := by
  have hsub : evalInterval n ⊆ Finset.range (q n) := by
    intro x hx
    exact Finset.mem_range.mpr
      (lt_of_le_of_lt (Finset.mem_Icc.mp hx).2 (q_bound n hn))
  unfold matrix2 penaltyMatrixEntry
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hxq : x < q n := Finset.mem_range.mp (hsub hx)
    have hval : ((x : ZMod (q n)).val = x) := ZMod.val_natCast_of_lt hxq
    rw [basisCos_eq_basisFunction n S x hx hn,
      basisCos_eq_basisFunction n T x hx hn]
    simp [Psi, hval, hx]
  · intro x hx hx'
    have hval : ((x : ZMod (q n)).val = x) :=
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hx)
    simp [Psi, hval, hx']

end KrafftSieve
