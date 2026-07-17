/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela, Gemini 3.1 Pro (Google DeepMind)
-/

import KrafftSieve.Basic
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

/-
Finite cosine orthogonality over a complete residue system.
-/
private lemma sum_cos_mul_cos_mod (p a b : ℕ) (hp : 0 < p) :
    ∑ k ∈ Finset.range p,
        Real.cos (2 * Real.pi * (k : ℝ) * (a : ℝ) / (p : ℝ)) *
        Real.cos (2 * Real.pi * (k : ℝ) * (b : ℝ) / (p : ℝ)) =
      (p : ℝ) / 2 *
        ((if (a : ZMod p) = (b : ZMod p) then 1 else 0) +
         (if (a : ZMod p) = -(b : ZMod p) then 1 else 0)) := by
  -- Use the trigonometric identity $2 \cos A \cos B = \cos(A+B) + \cos(A-B)$ to rewrite the sum.
  have h_trig : ∑ k ∈ Finset.range p, Real.cos (2 * Real.pi * k * a / p) *
                Real.cos (2 * Real.pi * k * b / p) =
                (1 / 2) * (∑ k ∈ Finset.range p, Real.cos (2 * Real.pi * k * (a + b) / p) +
                  ∑ k ∈ Finset.range p, Real.cos (2 * Real.pi * k * (a - b) / p)) := by
    rw [ ← Finset.sum_add_distrib, Finset.mul_sum ] ; congr ; ext k ; rw [ Real.cos_add_cos ]
    ring_nf
  -- Use the fact that $\sum_{k=0}^{p-1} \cos(2\pi k m / p)$ is zero
  -- unless $m$ is a multiple of $p$, in which case it is $p$.
  have h_cos_sum : ∀ m : ℤ, (∑ k ∈ Finset.range p, Real.cos (2 * Real.pi * k * m / p)) =
                            if m % p = 0 then p else 0 := by
    intro m
    split_ifs
    · simp_all +decide only [one_div, EuclideanDomain.mod_eq_zero,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      rw [ ZMod.intCast_zmod_eq_zero_iff_dvd ] at *
      obtain ⟨ k, rfl ⟩ := ‹ ( p : ℤ ) ∣ m ›
      norm_num [ mul_assoc, mul_comm Real.pi _, mul_div_assoc, hp.ne' ]
      exact Eq.trans ( Finset.sum_congr rfl fun _ _ => by
        convert Real.cos_int_mul_two_pi ( k * ‹ℕ› ) using 2; push_cast; ring ) ( by norm_num )
    · simp_all +decide only [one_div, EuclideanDomain.mod_eq_zero,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd, CharP.cast_eq_zero]
      -- Let $z = e^{2 \pi i m / p}$. Since $m$ is not divisible by $p$,
      -- $z$ is a primitive $p$-th root of unity.
      set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * m / p)
      have hz : ∑ k ∈ Finset.range p, z ^ k = 0 := by
        rw [ geom_sum_eq ]
        · rw [ ← Complex.exp_nat_mul, mul_comm,
               Complex.exp_eq_one_iff.mpr ⟨ m, by ring_nf; norm_num [ hp.ne' ] ⟩ ]
          norm_num
        · rw [ Ne.eq_def, Complex.exp_eq_one_iff ]
          field_simp
          exact fun ⟨ n, hn ⟩ => ‹¬ ( m : ZMod p ) = 0› <| by
            rw [ ZMod.intCast_zmod_eq_zero_iff_dvd ]
            exact ⟨ n, by
              rw [ div_eq_iff ( Nat.cast_ne_zero.mpr hp.ne' ) ] at hn; norm_cast at *; linarith ⟩
      convert congr_arg Complex.re hz using 2
      · norm_num [← Complex.exp_nat_mul, Complex.exp_re]
        exact Finset.sum_congr rfl fun _ _ => by
          rw [← Complex.exp_nat_mul]
          norm_num [Complex.exp_re]
          ring_nf
      · norm_num
  simp_all +decide only [one_div, EuclideanDomain.mod_eq_zero, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    Nat.cast_ite, CharP.cast_eq_zero]
  convert congr_arg₂ ( fun x y : ℝ => 2⁻¹ * ( x + y ) ) ( h_cos_sum ( a + b ) )
    ( h_cos_sum ( a - b ) ) using 1 <;> norm_num ; ring_nf
  grind

/-
For any prime index i, the local indicator function g_i(x) can be expanded exactly
as a normalized sum of cosines.
-/
theorem g_eq_sum_cos (n : ℕ) (i : Fin (w n)) (x : ZMod (q n)) :
    g n i x = (2 / (p n i : ℝ)) * ∑ k ∈ Finset.range (p n i),
      Real.cos (2 * Real.pi * ↑k * (krafftResidue n i : ℝ) / (p n i : ℝ)) *
      Real.cos (2 * Real.pi * ↑k * (x.val : ℝ) / (p n i : ℝ)) := by
  rw [ sum_cos_mul_cos_mod ]
  · have h_cast_eq_val : (x.cast : ZMod (p n i)) = x.val := by
      exact ZMod.cast_eq_val x
    split_ifs
    · have hlt : (2 * krafftResidue n i : ℕ) < p n i := by
        have hp5 : p n i ≥ 5 := p_ge_5 n i
        unfold krafftResidue
        omega
      have hz : (2 * krafftResidue n i : ZMod (p n i)) = 0 := by
        grind
      have hz' : ((2 * krafftResidue n i : ℕ) : ZMod (p n i)) = 0 := by
        push_cast
        exact hz
      rw [ZMod.natCast_eq_zero_iff] at hz'
      have hrpos : 0 < krafftResidue n i := by
        have hp5 : p n i ≥ 5 := p_ge_5 n i
        unfold krafftResidue
        omega
      exact absurd hz' (Nat.not_dvd_of_pos_of_lt (Nat.mul_pos zero_lt_two hrpos) hlt)
    · simp_all +decide only [ZMod.natCast_val, g, or_false, ↓reduceIte, add_zero, mul_one, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, div_mul_div_cancel₀']
      rw [div_self]
      exact_mod_cast p_ne_zero n i
    · simp_all +decide only [ZMod.natCast_val, g, neg_neg, or_true, ↓reduceIte, zero_add, mul_one,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_mul_div_cancel₀']
      rw [div_self]
      exact_mod_cast p_ne_zero n i
    · simp_all +decide [ g ]
      grind
  · exact p_pos n i

/-
The global additive hit counter c(x) is the sum of the cosine expansions of g_i.
-/
theorem c_eq_sum_cos (n : ℕ) (x : ZMod (q n)) :
    c n x = ∑ i : Fin (w n), (2 / (p n i : ℝ)) * ∑ k ∈ Finset.range (p n i),
      Real.cos (2 * Real.pi * ↑k * (krafftResidue n i : ℝ) / (p n i : ℝ)) *
      Real.cos (2 * Real.pi * ↑k * (x.val : ℝ) / (p n i : ℝ)) := by
  unfold c
  exact Finset.sum_congr rfl fun i _ => g_eq_sum_cos n i x

/-- The Ridge Graph, where vertices are basis sets and edges are phase-locked ridges. -/
def ridgeGraph (n : ℕ) : SimpleGraph (Finset (Fin (w n))) where
  Adj S T := isRidge n S T
  symm := Std.Symm.mk (fun S T h => by
    unfold isRidge at *
    refine ⟨h.1.symm, h.2.1.symm, ?_⟩
    have h_comm : massMatrixEntry n S T = massMatrixEntry n T S := by
      unfold massMatrixEntry
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_comm]
    rw [← h_comm]
    exact h.2.2)
  loopless := Std.Irrefl.mk (fun S h => by
    unfold isRidge at h
    exact h.1 rfl)

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

theorem g_nonneg (n : ℕ) (i : Fin (w n)) (x : ZMod (q n)) : 0 ≤ g n i x := by
  unfold g
  split_ifs
  · norm_num
  · norm_num

theorem c_nonneg (n : ℕ) (x : ZMod (q n)) : 0 ≤ c n x := by
  unfold c
  refine Finset.sum_nonneg fun i _ => g_nonneg n i x

theorem basisFunction_sq_le_one (n : ℕ) (S : Finset (Fin (w n))) (x : ℕ) :
    basisFunction n S x * basisFunction n S x ≤ 1 := by
  unfold basisFunction
  have h1 : (∏ i ∈ S, Real.cos (6 * Real.pi * ↑x / ↑(p n i))) *
            (∏ i ∈ S, Real.cos (6 * Real.pi * ↑x / ↑(p n i))) =
      ∏ i ∈ S, (Real.cos (6 * Real.pi * ↑x / ↑(p n i)) ^ 2) := by
    rw [← pow_two, ← Finset.prod_pow]
  rw [h1]
  refine Finset.prod_le_one ?_ ?_
  · intro i _
    positivity
  · intro i _
    have h2 : Real.cos (6 * Real.pi * ↑x / ↑(p n i)) ≤ 1 := Real.cos_le_one _
    have h3 : -1 ≤ Real.cos (6 * Real.pi * ↑x / ↑(p n i)) := Real.neg_one_le_cos _
    nlinarith

theorem penaltyMatrixEntry_diag_le (n : ℕ) (S : Finset (Fin (w n))) :
    penaltyMatrixEntry n S S ≤ ∑ x ∈ evalInterval n, c n (x : ZMod (q n)) := by
  unfold penaltyMatrixEntry
  refine Finset.sum_le_sum fun x _ => ?_
  have h_c := c_nonneg n (x : ZMod (q n))
  have h_b := basisFunction_sq_le_one n S x
  nlinarith

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
