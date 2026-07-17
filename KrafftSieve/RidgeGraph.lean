/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela, Gemini 3.1 Pro (Google DeepMind)
-/

import KrafftSieve.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Ridge Graph Formalization

This module defines the basis functions, the mass matrix $B$, and the penalty matrix $A$
for the restricted $k$-depth subspace. It translates the discrete Sieve matrices
into graph-theoretic structures defined by Dirichlet kernel phase-locking.
-/

namespace KrafftSieve

open scoped BigOperators Real

noncomputable section

/-- A single cross-harmonic basis function $B_S(x) = \prod_{p \in S} \cos(6\pi x / p)$. -/
def basisFunction (n : ℕ) (S : Finset (Fin (w n))) (x : ℕ) : ℝ :=
  ∏ i ∈ S, Real.cos (6 * Real.pi * (x : ℝ) / (p n i : ℝ))

/-- The discrete mass matrix entry $B_{ST} = \sum_{x \in \mathcal{A}_n} B_S(x) B_T(x)$. -/
def massMatrixEntry (n : ℕ) (S T : Finset (Fin (w n))) : ℝ :=
  ∑ x ∈ evalInterval n, basisFunction n S x * basisFunction n T x

/-- The discrete penalty matrix entry $A_{ST} = \sum_{x \in \mathcal{A}_n} c(x) B_S(x) B_T(x)$. -/
def penaltyMatrixEntry (n : ℕ) (S T : Finset (Fin (w n))) : ℝ :=
  ∑ x ∈ evalInterval n, c n (x : ZMod (q n)) * basisFunction n S x * basisFunction n T x

/-- The discrete Dirichlet kernel $D_N(\omega) = \sum_{x \in \mathcal{A}_n} \cos(\omega x)$. -/
def discreteDirichletKernel (n : ℕ) (ω : ℝ) : ℝ :=
  ∑ x ∈ evalInterval n, Real.cos (ω * (x : ℝ))

/-- The threshold for a phase-locked ridge. -/
def ridgeThreshold (n : ℕ) : ℝ := (evalInterval n).card / 2

/-- An edge exists between S and T if they are distinct, disjoint and their inner product is highly
constructive. -/
def isRidge (n : ℕ) (S T : Finset (Fin (w n))) : Prop :=
  S ≠ T ∧ Disjoint S T ∧ massMatrixEntry n S T > ridgeThreshold n

/-- The Ridge Graph, where vertices are basis sets and edges are phase-locked ridges. -/
def ridgeGraph (n : ℕ) : SimpleGraph (Finset (Fin (w n))) where
  Adj S T := isRidge n S T
  symm := ⟨fun {S T} h => by
    unfold isRidge at *
    refine ⟨h.1.symm, h.2.1.symm, ?_⟩
    have h_comm : massMatrixEntry n S T = massMatrixEntry n T S := by
      unfold massMatrixEntry
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_comm]
    rw [← h_comm]
    exact h.2.2⟩
  loopless := ⟨fun S h => by
    unfold isRidge at h
    exact h.1 rfl⟩

/-- A test vector based on a clique in the Ridge Graph.
It assigns weight 1 to vertices in the clique, and 0 otherwise. -/
def cliqueTestVector (n : ℕ) (C : Finset (Finset (Fin (w n)))) (S : Finset (Fin (w n))) : ℝ :=
  if S ∈ C then 1 else 0

/-- The total mass $Q_1 = \lambda^T B \lambda$ evaluated with the clique test vector. -/
def testMass (n : ℕ) (C : Finset (Finset (Fin (w n)))) : ℝ :=
  ∑ S ∈ C, ∑ T ∈ C, massMatrixEntry n S T

/-- The total penalty $Q_2 = \lambda^T A \lambda$ evaluated with the clique test vector. -/
def testPenalty (n : ℕ) (C : Finset (Finset (Fin (w n)))) : ℝ :=
  ∑ S ∈ C, ∑ T ∈ C, penaltyMatrixEntry n S T

/-- If C is a clique in the Ridge Graph, the off-diagonal mass is strictly bounded below
by the ridge threshold. -/
theorem testMass_lower_bound (n : ℕ) (C : Finset (Finset (Fin (w n))))
    (h_clique : (ridgeGraph n).IsClique (C : Set (Finset (Fin (w n))))) :
    testMass n C ≥ (C.card : ℝ) * (C.card - 1 : ℝ) * (ridgeThreshold n) := by
  have h_split : ∀ S ∈ C, ∑ T ∈ C, massMatrixEntry n S T =
                          massMatrixEntry n S S + ∑ T ∈ C \ {S}, massMatrixEntry n S T := by
    intro S hS
    have h_sub : {S} ⊆ C := Finset.singleton_subset_iff.mpr hS
    have h_eq := Finset.sum_sdiff (f := fun T => massMatrixEntry n S T) h_sub
    rw [Finset.sum_singleton] at h_eq
    linarith
  have h_diag : ∀ S ∈ C, massMatrixEntry n S S ≥ 0 := by
    intro S _
    unfold massMatrixEntry
    refine Finset.sum_nonneg fun x _ => ?_
    nlinarith
  have h_offdiag : ∀ S ∈ C, ∀ T ∈ C \ {S}, massMatrixEntry n S T > ridgeThreshold n := by
    intro S hS T hT
    have h_sdiff := Finset.mem_sdiff.mp hT
    have hT_C : T ∈ C := h_sdiff.1
    have h_neq : S ≠ T := by
      intro h_eq
      have h_mem : T ∈ ({S} : Finset (Finset (Fin (w n)))) := by
        rw [h_eq]; exact Finset.mem_singleton_self T
      exact h_sdiff.2 h_mem
    have h_adj : (ridgeGraph n).Adj S T := h_clique hS hT_C h_neq
    exact h_adj.2.2
  have h_inner : ∀ S ∈ C, ∑ T ∈ C, massMatrixEntry n S T ≥
                          ((C.card : ℝ) - 1) * ridgeThreshold n := by
    intro S hS
    rw [h_split S hS]
    have h1 : massMatrixEntry n S S ≥ 0 := h_diag S hS
    have h2 : ∑ T ∈ C \ {S}, massMatrixEntry n S T ≥ ∑ T ∈ C \ {S}, ridgeThreshold n := by
      refine Finset.sum_le_sum fun T hT => ?_
      exact le_of_lt (h_offdiag S hS T hT)
    have h3 : ∑ T ∈ C \ {S}, ridgeThreshold n = (((C \ {S}).card) : ℝ) * ridgeThreshold n := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    have h4 : (C \ {S}).card = C.card - 1 := by
      rw [Finset.card_sdiff]
      have h_inter2 : C ∩ {S} = {S} :=
        Finset.inter_eq_right.mpr (Finset.singleton_subset_iff.mpr hS)
      rw [Finset.inter_comm] at h_inter2
      rw [h_inter2, Finset.card_singleton]
    have h5 : (((C \ {S}).card) : ℝ) = (C.card : ℝ) - 1 := by
      rw [h4]
      have hcard : 1 ≤ C.card := Finset.one_le_card.mpr ⟨S, hS⟩
      norm_num [Nat.cast_sub hcard]
    rw [h5] at h3
    calc
      massMatrixEntry n S S + ∑ T ∈ C \ {S}, massMatrixEntry n S T ≥
          0 + ∑ T ∈ C \ {S}, ridgeThreshold n := add_le_add h1 h2
      _ = ((C.card : ℝ) - 1) * ridgeThreshold n := by rw [h3]; ring
  unfold testMass
  have h_total : ∑ S ∈ C, ∑ T ∈ C, massMatrixEntry n S T ≥
                 ∑ S ∈ C, (((C.card : ℝ) - 1) * ridgeThreshold n) := by
    refine Finset.sum_le_sum fun S hS => h_inner S hS
  have h_final : ∑ S ∈ C, (((C.card : ℝ) - 1) * ridgeThreshold n) =
                 (C.card : ℝ) * ((C.card : ℝ) - 1) * ridgeThreshold n := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [h_final] at h_total
  linarith

/-- The total penalty $Q_2 = \lambda^T A \lambda$ is bounded from above because
off-diagonal penalty terms undergo destructive interference (assumed $\le 0$ for this bound),
leaving mostly the diagonal mass which is bounded by the total sum of hits. -/
theorem testPenalty_upper_bound (n : ℕ) (C : Finset (Finset (Fin (w n))))
    (h_clique : (ridgeGraph n).IsClique (C : Set (Finset (Fin (w n))))) :
    testPenalty n C ≤ (C.card : ℝ) * (∑ x ∈ evalInterval n, c n (x : ZMod (q n))) := by
  -- Proof by destructive interference of non-active primes
  sorry

/-- The Rayleigh Quotient \mu = Q_2 / Q_1 can be driven strictly below 1
for a sufficiently large clique C in the Ridge Graph. -/
theorem rayleigh_quotient_bound (n : ℕ) (C : Finset (Finset (Fin (w n))))
    (h_clique : (ridgeGraph n).IsClique (C : Set (Finset (Fin (w n)))))
    (h_large : (C.card : ℝ) >
      1 + 2 * (∑ x ∈ evalInterval n, c n (x : ZMod (q n))) / (evalInterval n).card) :
    testPenalty n C / testMass n C < 1 := by
  -- Combines testMass_lower_bound and testPenalty_upper_bound
  sorry

/-- Product-to-sum expansion of a product of cosines over a `Finset`, indexed by a
powerset of sign choices. -/
theorem dirichlet_prod_cos_expand {ι : Type*} [DecidableEq ι] (A : Finset ι) (θ : ι → ℝ) :
    ∏ i ∈ A, Real.cos (θ i) =
      (2 ^ A.card : ℝ)⁻¹ *
        ∑ B ∈ A.powerset, Real.cos ((∑ i ∈ B, θ i) - ∑ i ∈ A \ B, θ i) := by
  induction A using Finset.induction with
  | empty => norm_num
  | @insert a A ha ih =>
    rw [Finset.card_insert_of_notMem ha, Finset.prod_insert ha, ih,
      Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]
    simp only [Finset.mul_sum]
    rw [pow_succ]
    refine Finset.sum_congr rfl fun B hB => ?_
    have haB : a ∉ B := fun h => ha (Finset.mem_powerset.mp hB h)
    have h1 : insert a A \ B = insert a (A \ B) := Finset.insert_sdiff_of_notMem A haB
    have h2 : insert a A \ insert a B = A \ B := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]; constructor
      · rintro ⟨(rfl | hx), hx2⟩
        · exact absurd (Or.inl rfl) hx2
        · exact ⟨hx, fun h => hx2 (Or.inr h)⟩
      · rintro ⟨hx, hx2⟩
        refine ⟨Or.inr hx, fun h => ?_⟩
        rcases h with rfl | h
        · exact ha hx
        · exact hx2 h
    have haAB : a ∉ A \ B := fun h => ha (Finset.mem_sdiff.mp h).1
    rw [h1, Finset.sum_insert haAB, Finset.sum_insert haB, h2]
    have key : ∀ s u : ℝ, Real.cos (s - (θ a + u)) + Real.cos (θ a + s - u)
        = 2 * Real.cos (θ a) * Real.cos (s - u) := by
      intro s u
      have e1 : s - (θ a + u) = (s - u) - θ a := by ring
      have e2 : θ a + s - u = θ a + (s - u) := by ring
      rw [e1, e2, Real.cos_sub, Real.cos_add]; ring
    rw [key]; ring

/-- The exact evaluation of the mass matrix entry via discrete Dirichlet kernels,
for disjoint basis sets. -/
theorem massMatrixEntry_eq_dirichlet_sum_of_disjoint (n : ℕ) (S T : Finset (Fin (w n)))
    (h_disjoint : Disjoint S T) :
    massMatrixEntry n S T =
      (2 ^ (S ∪ T).card : ℝ)⁻¹ *
        ∑ B ∈ (S ∪ T).powerset,
          discreteDirichletKernel n
            (6 * Real.pi * (∑ i ∈ B, (p n i : ℝ)⁻¹ - ∑ i ∈ (S ∪ T) \ B, (p n i : ℝ)⁻¹)) := by
  unfold massMatrixEntry basisFunction discreteDirichletKernel
  have h_prod : ∀ x : ℕ, (∏ i ∈ S, Real.cos (6 * Real.pi * ↑x / ↑(p n i))) *
                (∏ i ∈ T, Real.cos (6 * Real.pi * ↑x / ↑(p n i))) =
                ∏ i ∈ S ∪ T, Real.cos (6 * Real.pi * ↑x / ↑(p n i)) := by
    intro x
    rw [Finset.prod_union h_disjoint]
  simp_rw [h_prod]
  have h_expand : ∀ x : ℕ, ∏ i ∈ S ∪ T, Real.cos (6 * Real.pi * ↑x / ↑(p n i)) =
      (2 ^ (S ∪ T).card : ℝ)⁻¹ *
        ∑ B ∈ (S ∪ T).powerset, Real.cos ((∑ i ∈ B, 6 * Real.pi * ↑x / ↑(p n i)) -
                                           ∑ i ∈ (S ∪ T) \ B, 6 * Real.pi * ↑x / ↑(p n i)) := by
    intro x
    exact dirichlet_prod_cos_expand (S ∪ T) (fun i => 6 * Real.pi * (x : ℝ) / (p n i : ℝ))
  simp_rw [h_expand]
  have h_mul_sum : ∀ (c : ℝ) (s : Finset ℕ) (f : ℕ → ℝ), ∑ x ∈ s, c * f x = c * ∑ x ∈ s, f x :=
    fun c s f => (Finset.mul_sum (s:=s) (f:=f) (a:=c)).symm
  rw [h_mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun B _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp_rw [div_eq_mul_inv]
  have e1 : ∑ i ∈ B, 6 * Real.pi * (x : ℝ) * (p n i : ℝ)⁻¹ =
            (6 * Real.pi * (x : ℝ)) * ∑ i ∈ B, (p n i : ℝ)⁻¹ := by
    have h : ∀ i ∈ B, 6 * Real.pi * (x : ℝ) * (p n i : ℝ)⁻¹ =
                      (6 * Real.pi * (x : ℝ)) * (p n i : ℝ)⁻¹ := fun _ _ => by ring
    rw [Finset.sum_congr rfl h]
    exact (Finset.mul_sum (s:=B) (f:=fun i => (p n i : ℝ)⁻¹) (a:=(6 * Real.pi * (x : ℝ)))).symm
  have e2 : ∑ i ∈ (S ∪ T) \ B, 6 * Real.pi * (x : ℝ) * (p n i : ℝ)⁻¹ =
            (6 * Real.pi * (x : ℝ)) * ∑ i ∈ (S ∪ T) \ B, (p n i : ℝ)⁻¹ := by
    have h : ∀ i ∈ (S ∪ T) \ B, 6 * Real.pi * (x : ℝ) * (p n i : ℝ)⁻¹ =
                                (6 * Real.pi * (x : ℝ)) * (p n i : ℝ)⁻¹ := fun _ _ => by ring
    rw [Finset.sum_congr rfl h]
    exact (Finset.mul_sum (s:=(S ∪ T) \ B)
                          (f := fun i => (p n i : ℝ)⁻¹)
                          (a := (6 * Real.pi * (x : ℝ)))).symm
  rw [e1, e2]
  ring

end

end KrafftSieve
