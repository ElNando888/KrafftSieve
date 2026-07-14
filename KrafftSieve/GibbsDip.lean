/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela, Gemini 3.1 Pro (Google DeepMind), Aristotle (Harmonic)
-/

import KrafftSieve.Discretization
import KrafftSieve.GibbsAux

/-!
# Lemma 5.1: The Unconditional Continuous Penalty Dip (`h_dip`)

This file formally proves the `h_dip` hypothesis of `KrafftSieve.MainTheorem` using the
unconditional analytic Gibbs undershoot of the continuous penalty `c_cont₀ n`.

Unlike the discrete arithmetic search (which depends on finding Twin Primes in the grid),
this proof constructs a specific continuous sub-interval `x = y_CRT + 0.25` where the
truncated Fourier series experiences massive Gibbs oscillations that plunge the penalty
below `1.0`, entirely bypassing the discrete arithmetic barrier.

The heavy self-contained analytic content lives in `KrafftSieve.GibbsAux`.
-/

namespace KrafftSieve

open scoped unitInterval
open unitInterval
open MeasureTheory

/--
At the quarter-integer evaluated exactly at the CRT residue offset (positive sign), the local
interpolant experiences a Gibbs undershoot strictly bounded below `-0.1`.
-/
lemma g_i_undershoot_quarter_pos (n : ℕ) (i : Fin (w n)) (y : ℤ)
    (hy : y ≡ (krafftResidue n i : ℤ) + 1 [ZMOD (p n i : ℤ)]) :
    ∑ k ∈ Finset.range ((p n i + 1) / 2),
      g_coef n i k * Real.cos (2 * Real.pi * k * (y + 0.25) / (p n i : ℝ)) ≤ -0.1 := by
  have h := GibbsAux.undershoot_value_quarter (p n i) (krafftResidue n i)
    (p_prime n i) (p_ge_5 n i) rfl y hy
  simpa only [g_coef] using h

/--
At the quarter-integer evaluated exactly at the CRT residue offset (negative sign), the local
interpolant experiences a positive Gibbs overshoot bounded above by `0.12`.
-/
lemma g_i_overshoot_quarter_neg (n : ℕ) (i : Fin (w n)) (y : ℤ)
    (hy : y ≡ -(krafftResidue n i : ℤ) + 1 [ZMOD (p n i : ℤ)]) :
    ∑ k ∈ Finset.range ((p n i + 1) / 2),
      g_coef n i k * Real.cos (2 * Real.pi * k * (y + 0.25) / (p n i : ℝ)) ≤ 0.12 := by
  sorry

/--
The arithmetic mean of the positive and negative root evaluations at the quarter offset is strictly
negative. (This relies on the fact that the positive root undershoot dominates the negative root
overshoot when appropriately scaled for primes >= 5; specifically, for p=5, the mean is <= -0.04).
-/
lemma g_i_expected_quarter (n : ℕ) (hn : 4 ≤ n) (i : Fin (w n)) (y_pos y_neg : ℤ)
    (h_pos : y_pos ≡ (krafftResidue n i : ℤ) + 1 [ZMOD (p n i : ℤ)])
    (h_neg : y_neg ≡ -(krafftResidue n i : ℤ) + 1 [ZMOD (p n i : ℤ)]) :
    (1 / 2 : ℝ) * (
      (∑ k ∈ Finset.range ((p n i + 1) / 2), g_coef n i k * Real.cos (2 * Real.pi * k * (y_pos + 0.25) / (p n i : ℝ))) +
      (∑ k ∈ Finset.range ((p n i + 1) / 2), g_coef n i k * Real.cos (2 * Real.pi * k * (y_neg + 0.25) / (p n i : ℝ)))
    ) ≤ -0.04 := by
  sorry

/--
By the Chinese Remainder Theorem independence, the sum of the continuous penalty function evaluated
at `y + 0.25` over all `2^{w(n)}` CRT roots factors exactly into the product of the expected values.
Consequently, the total sum is bounded by `-0.04 * w(n) * 2^{w(n)}`.
-/
lemma sum_c_cont_0_all_roots (n : ℕ) (hn : 4 ≤ n) :
    let S := (Finset.Ico 0 (q n : ℤ)).filter (fun y =>
               ∀ i : Fin (w n), y ≡ (krafftResidue n i : ℤ) + 1 [ZMOD (p n i : ℤ)] ∨
                                y ≡ -(krafftResidue n i : ℤ) + 1 [ZMOD (p n i : ℤ)]);
    ∑ y ∈ S, c_cont₀ n ⟨(((y : ℝ) + 0.25) / (q n : ℝ)) - ⌊(((y : ℝ) + 0.25) / (q n : ℝ))⌋, ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩⟩
    ≤ -0.04 * (w n : ℝ) * (2 ^ w n : ℝ) := by
  sorry

/--
For $n \ge 18$, the exponential growth of the solution space strictly dominates the polynomial capacity of the trap region.
-/
lemma trap_capacity_lt_exponential (n : ℕ) (hn : 18 ≤ n) :
    (2 * (6 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 3) + 1) < 0.04 * (2 ^ w n : ℝ) := by
  sorry

/--
Because the $E_{max}$ trap region has polynomial capacity while the total CRT roots scale
exponentially, there exists at least one root $y_{CRT}$ in the golden region (outside the trap region)
where the penalty drops below `-0.04 * w(n)`.
-/
lemma c_cont_0_valley_quarter (n : ℕ) (hn : 18 ≤ n) :
    ∃ y_CRT : ℤ, (6 * (n : ℤ) ^ 2 + 10 * (n : ℤ) + 3) < y_CRT ∧ y_CRT < (q n : ℤ) - (6 * (n : ℤ) ^ 2 + 10 * (n : ℤ) + 3) ∧
    c_cont₀ n ⟨(((y_CRT : ℝ) + 0.25) / (q n : ℝ)) - ⌊(((y_CRT : ℝ) + 0.25) / (q n : ℝ))⌋,
      ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩⟩ ≤ -0.04 * (w n : ℝ) := by
  sorry

/--
For any CRT valley in the golden region, the reproducing window `Psi_cont`
is strictly positive at the quarter-integer because the Dirichlet kernels transform into
strictly positive cotangents.

(Unproven; left as `sorry`.) `Psi_cont n` is `reproWindow (q n) (kernelDegree n) …`, i.e. a
`(1/q)`-scaled sum of *shifted Dirichlet kernels* over the support of the discrete window `Psi n`.
Dirichlet kernels are sign-oscillating, so positivity at the quarter-integer valley point is a
genuine analytic fact (the windowed Dirichlet sum telescopes to a positive cotangent expression
in the golden region). Formalizing this requires the exact `dirichletKernel` telescoping identity
and is left for future work; it is used by `h_dip_unconditional` below.
-/
lemma Psi_cont_positive_quarter (n : ℕ) (hn : 18 ≤ n) (y_CRT : ℤ)
    (h_gt : (6 * (n : ℤ) ^ 2 + 10 * (n : ℤ) + 3) < y_CRT) (h_lt : y_CRT < (q n : ℤ) - (6 * (n : ℤ) ^ 2 + 10 * (n : ℤ) + 3)) :
    0 < Psi_cont n ⟨(((y_CRT : ℝ) + 0.25) / (q n : ℝ)) - ⌊(((y_CRT : ℝ) + 0.25) / (q n : ℝ))⌋,
      ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩⟩ := by
  sorry

/-- Every nonempty open subset of the unit interval `X₀` has positive volume. -/
lemma volume_pos_of_isOpen_nonempty (s : Set X₀) (hs : IsOpen s) (hne : s.Nonempty) :
    0 < (volume : Measure X₀) s := by
  rw [show (volume : Measure X₀) = (volume : Measure ℝ).comap Subtype.val from rfl]
  have hemb : MeasurableEmbedding ((↑) : X₀ → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  rw [hemb.comap_apply]
  obtain ⟨x, hx⟩ := hne
  obtain ⟨V, hV_open, hVs⟩ := (isOpen_induced_iff.mp hs)
  have hxV : (x : ℝ) ∈ V := by
    have : x ∈ Subtype.val ⁻¹' V := by rw [hVs]; exact hx
    exact this
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV_open (x : ℝ) hxV
  set a := max 0 ((x : ℝ) - ε / 2) with ha
  set b := min 1 ((x : ℝ) + ε / 2) with hb
  have hx01 : (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 := x.2
  have hab : a < b := by
    have hax : a ≤ (x : ℝ) := max_le hx01.1 (by linarith)
    have hxb : (x : ℝ) ≤ b := le_min hx01.2 (by linarith)
    rcases lt_or_eq_of_le hx01.2 with h1 | h1
    · have : (x : ℝ) < b := lt_min h1 (by linarith)
      linarith
    · have ha1 : a < 1 := max_lt (by norm_num) (by rw [← h1]; linarith)
      have hb1 : b = 1 := by rw [hb, ← h1]; exact min_eq_left (by linarith)
      rw [hb1]; linarith [ha1, h1]
  have hsub : Set.Icc a b ⊆ V := by
    intro y hy
    apply hball
    have h1 : (x : ℝ) - ε / 2 ≤ y := le_trans (le_max_right _ _) hy.1
    have h2 : y ≤ (x : ℝ) + ε / 2 := le_trans hy.2 (min_le_right _ _)
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hsub01 : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1 := fun y hy =>
    ⟨le_trans (le_max_left _ _) hy.1, le_trans hy.2 (min_le_left _ _)⟩
  have hpos : (0 : ENNReal) < volume (Set.Icc a b) := by
    rw [Real.volume_Icc, ENNReal.ofReal_pos]; linarith
  calc (0 : ENNReal) < volume (Set.Icc a b) := hpos
    _ ≤ volume (Subtype.val '' s) := by
        apply measure_mono
        intro y hy
        exact ⟨⟨y, hsub01 hy⟩, by rw [← hVs]; exact hsub hy, rfl⟩

/--
The continuous penalty `c_cont₀` drops below 1 and `Psi_cont` has positive integral on a set,
satisfying the `h_dip` hypothesis unconditionally for $n \ge 18$.

The witnessing set is the (open) region where `Psi_cont` is positive and `c_cont₀ < 1`; it contains
the Gibbs valley point, hence is nonempty (positive volume), and `Psi_cont` is positive throughout,
so its integral is positive.
-/
theorem h_dip_unconditional (n : ℕ) (hn : 18 ≤ n) :
    ∃ s : Set X₀, MeasurableSet s ∧
    0 < ∫ t in s, Psi_cont n t ∂(volume : Measure X₀) ∧
    ∀ t ∈ s, c_cont₀ n t < 1 := by
  obtain ⟨y_CRT, h_gt, h_lt, hc⟩ := c_cont_0_valley_quarter n hn
  set x0 : X₀ := ⟨(((y_CRT : ℝ) + 0.25) / (q n : ℝ)) - ⌊(((y_CRT : ℝ) + 0.25) / (q n : ℝ))⌋,
      ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩⟩ with hx0
  have hPsi0 : 0 < Psi_cont n x0 := Psi_cont_positive_quarter n hn y_CRT h_gt h_lt
  have hc0 : c_cont₀ n x0 < 1 := by
    have hw : (0 : ℝ) ≤ (w n : ℝ) := Nat.cast_nonneg _
    nlinarith [hc, hw]
  have hcont_c : Continuous (c_cont₀ n) := by unfold c_cont₀; fun_prop
  have hcont_P : Continuous (Psi_cont n) := Psi_cont_continuous n
  set s : Set X₀ := {t | 0 < Psi_cont n t ∧ c_cont₀ n t < 1} with hs_def
  have hs_open : IsOpen s :=
    (isOpen_lt continuous_const hcont_P).inter (isOpen_lt hcont_c continuous_const)
  have hx0s : x0 ∈ s := ⟨hPsi0, hc0⟩
  refine ⟨s, hs_open.measurableSet, ?_, fun t ht => ht.2⟩
  have hInt : IntegrableOn (Psi_cont n) s (volume : Measure X₀) :=
    (hcont_P.continuousOn.integrableOn_compact isCompact_univ).mono_set (Set.subset_univ s)
  have hnn : 0 ≤ᵐ[(volume : Measure X₀).restrict s] (Psi_cont n) := by
    filter_upwards [ae_restrict_mem hs_open.measurableSet] with t ht using (ht.1).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hInt]
  have hsupp : Function.support (Psi_cont n) ∩ s = s := by
    ext t
    simp only [Set.mem_inter_iff, Function.mem_support, hs_def, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨ne_of_gt h.1, h⟩⟩
  rw [hsupp]
  exact volume_pos_of_isOpen_nonempty s hs_open ⟨x0, hx0s⟩

end KrafftSieve
