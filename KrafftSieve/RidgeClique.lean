
import KrafftSieve.OptimalWeights
import KrafftSieve.RidgeGraph
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace KrafftSieve
open scoped BigOperators

-- We want to express the indicator function g n i x as a sum of cosines.
-- g n i x = 1 if x = r n i or x = -r n i mod (p n i), and 0 otherwise.

open scoped Classical in
/-- The algebraic identity for the sum over a powerset of a product. -/
lemma sum_powerset_prod_eq_prod_add_one {ι : Type*} (I : Finset ι) (f : ι → ℝ) :
    ∑ S ∈ I.powerset, ∏ i ∈ S, f i = ∏ i ∈ I, (1 + f i) := by
  have : ∏ i ∈ I, (f i + 1) = ∑ S ∈ I.powerset, (∏ i ∈ S, f i) * ∏ i ∈ I \ S, (1 : ℝ) :=
    Finset.prod_add f (fun _ => 1) I
  simp only [Finset.prod_const_one, mul_one] at this
  rw [← this]
  refine Finset.prod_congr rfl (fun x _ => add_comm _ _)

/-
Fourier expansion of the symmetric pair of Krafft residues modulo a prime.
-/
lemma krafft_pair_fourier (p x : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (if (x : ZMod p) = (((p + 1) / 6 : ℕ) : ZMod p) ∨
        (x : ZMod p) = -(((p + 1) / 6 : ℕ) : ZMod p) then (1 : ℝ) else 0) =
      2 / (p : ℝ) +
      (4 / (p : ℝ)) * ∑ k ∈ Finset.Ico 1 ((p + 1) / 2),
        Real.cos (2 * Real.pi * (k : ℝ) * (((p + 1) / 6 : ℕ) : ℝ) / (p : ℝ)) *
        Real.cos (2 * Real.pi * (k : ℝ) * (x : ℝ) / (p : ℝ)) := by
  -- Let $r = \frac{p+1}{6}$.
  set r := (p + 1) / 6
  -- Consider the sum $\sum_{k=0}^{p-1} \cos\left(\frac{2\pi k (x - r)}{p}\right) +
  -- \cos\left(\frac{2\pi k (x + r)}{p}\right)$.
  have h_sum : ∑ k ∈ Finset.range p,
      (Real.cos (2 * Real.pi * k * (x - r) / p) + Real.cos (2 * Real.pi * k * (x + r) / p)) =
      p * (if x ≡ r [MOD p] ∨ x ≡ p - r [MOD p] then 1 else 0) := by
    have h_sum : ∀ m : ℤ, (∑ k ∈ Finset.range p, Real.cos (2 * Real.pi * k * m / p)) =
                          if m % p = 0 then p else 0 := by
      intro m
      split_ifs
      · simp_all +decide only [EuclideanDomain.mod_eq_zero, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
        rw [ ZMod.intCast_zmod_eq_zero_iff_dvd ] at *
        obtain ⟨ k, rfl ⟩ := ‹ ( p : ℤ ) ∣ m ›
        norm_num [ mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, hp.ne_zero ]
        exact Eq.trans ( Finset.sum_congr rfl fun _ _ => by
          rw [ Real.cos_eq_one_iff ] ; use k * ‹ℕ›; push_cast; ring ) ( by norm_num )
      · simp_all +decide only [EuclideanDomain.mod_eq_zero, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
          CharP.cast_eq_zero]
        -- Let $z = e^{2 \pi i m / p}$. Since $m$ is not divisible by $p$, $z$ is a primitive
        -- $p$-th root of unity.
        set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * m / p)
        have hz : ∑ k ∈ Finset.range p, z ^ k = 0 := by
          rw [ geom_sum_eq ]
          · rw [ ← Complex.exp_nat_mul, mul_comm,
              Complex.exp_eq_one_iff.mpr ⟨ m, by ring_nf; norm_num [ hp.ne_zero ] ⟩ ]
            norm_num
          · rw [ Ne.eq_def, Complex.exp_eq_one_iff ]
            field_simp
            exact fun ⟨ n, hn ⟩ => ‹¬ ( m : ZMod p ) = 0› <| by
              rw [ div_eq_iff ( Nat.cast_ne_zero.mpr hp.ne_zero ) ] at hn
              norm_cast at *
              aesop
        convert congr_arg Complex.re hz using 2
        · norm_num [← Complex.exp_nat_mul, Complex.exp_re]
          exact Finset.sum_congr rfl fun _ _ => by
            rw [← Complex.exp_nat_mul]
            norm_num [Complex.exp_re]
            ring_nf
        · rfl
    convert congr_arg₂ ( · + · ) ( h_sum ( x - r ) ) ( h_sum ( x + r ) ) using 1
    · norm_num [ Finset.sum_add_distrib ]
    · split_ifs
      · simp_all +decide only [EuclideanDomain.mod_eq_zero, Nat.cast_ite, CharP.cast_eq_zero,
        ← Int.natCast_modEq_iff, mul_one, left_eq_add, Nat.cast_eq_zero]
        have := Int.dvd_sub ‹ ( p : ℤ ) ∣ x + r › ‹ ( p : ℤ ) ∣ x - r ›; norm_num at this
        norm_cast at this; have := Nat.dvd_trans ( Nat.dvd_refl p ) this
        simp_all +decide only [Int.natCast_modEq_iff, ← two_mul, Nat.Prime.dvd_mul]
        exact absurd
          ( this.resolve_left ( Nat.not_dvd_of_pos_of_lt ( by norm_num ) ( by linarith ) ) )
          ( Nat.not_dvd_of_pos_of_lt ( Nat.div_pos ( by linarith ) ( by norm_num ) )
                                     ( Nat.div_lt_of_lt_mul <| by linarith ) )
      · simp_all +decide [ ← Int.natCast_modEq_iff ]
      · simp_all +decide [ ← Int.natCast_modEq_iff ]
      · simp_all +decide only [EuclideanDomain.mod_eq_zero, Nat.cast_ite, CharP.cast_eq_zero,
        ← Int.natCast_modEq_iff, mul_one, add_zero, Nat.cast_eq_zero]
        cases ‹ ( x : ℤ ) ≡ r [ZMOD p] ∨ _› <;> simp_all +decide only
          [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast, Int.cast_add,
          ← ZMod.intCast_eq_intCast_iff, sub_self, not_true_eq_false]
        rw [ Nat.cast_sub ( show r ≤ p from Nat.div_le_of_le_mul <| by linarith ) ] at * ; aesop
      · simp_all +decide [ ← Int.natCast_modEq_iff, Int.ModEq,
          Int.emod_eq_emod_iff_emod_sub_eq_zero ]
      · simp_all +decide [ ← Int.natCast_modEq_iff, Int.ModEq,
          Int.emod_eq_emod_iff_emod_sub_eq_zero ]
      · simp_all +decide only [EuclideanDomain.mod_eq_zero, Nat.cast_ite, CharP.cast_eq_zero,
          ← Int.natCast_modEq_iff, not_or, mul_zero, zero_add]
        simp_all +decide only [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_eq_intCast_iff,
          Int.cast_natCast, Int.cast_sub, Int.cast_add]
        simp_all +decide only [sub_eq_iff_eq_add, zero_add, not_false_eq_true,
          add_eq_zero_iff_eq_neg]
        rw [ Nat.cast_sub ( show r ≤ p from Nat.div_le_of_le_mul <| by linarith ) ] at * ; aesop
      · simp_all +decide [ ← Int.natCast_modEq_iff ]
  -- Split the sum into two parts: one from $k=0$ to $k=\frac{p-1}{2}$ and one from
  -- $k=\frac{p+1}{2}$ to $k=p-1$.
  have h_split : ∑ k ∈ Finset.range p,
      (Real.cos (2 * Real.pi * k * (x - r) / p) + Real.cos (2 * Real.pi * k * (x + r) / p)) =
      2 + 2 * ∑ k ∈ Finset.Ico 1 ((p + 1) / 2),
      (Real.cos (2 * Real.pi * k * (x - r) / p) + Real.cos (2 * Real.pi * k * (x + r) / p)) := by
    have h_split : ∑ k ∈ Finset.range p,
        (Real.cos (2 * Real.pi * k * (x - r) / p) + Real.cos (2 * Real.pi * k * (x + r) / p)) =
        2 + ∑ k ∈ Finset.Ico 1 ((p + 1) / 2),
        (Real.cos (2 * Real.pi * k * (x - r) / p) + Real.cos (2 * Real.pi * k * (x + r) / p)) +
        ∑ k ∈ Finset.Ico ((p + 1) / 2) p,
        (Real.cos (2 * Real.pi * k * (x - r) / p) + Real.cos (2 * Real.pi * k * (x + r) / p)) := by
      rw [ Finset.sum_Ico_eq_sub _ _, Finset.sum_Ico_eq_sub _ _ ] <;> norm_num; all_goals omega
    -- Notice that $\sum_{k=\frac{p+1}{2}}^{p-1} \cos\left(\frac{2\pi k (x - r)}{p}\right) +
    -- \cos\left(\frac{2\pi k (x + r)}{p}\right)$ is equal to
    -- $\sum_{k=1}^{\frac{p-1}{2}} \cos\left(\frac{2\pi (p - k) (x - r)}{p}\right) +
    -- \cos\left(\frac{2\pi (p - k) (x + r)}{p}\right)$.
    have h_symm : ∑ k ∈ Finset.Ico ((p + 1) / 2) p,
        (Real.cos (2 * Real.pi * k * (x - r) / p) + Real.cos (2 * Real.pi * k * (x + r) / p)) =
        ∑ k ∈ Finset.Ico 1 ((p + 1) / 2), (Real.cos (2 * Real.pi * (p - k) * (x - r) / p) +
        Real.cos (2 * Real.pi * (p - k) * (x + r) / p)) := by
      apply Finset.sum_bij (fun k hk => p - k)
      · cases Nat.Prime.eq_two_or_odd hp <;> simp_all +arith +decide only [Order.lt_two_iff,
        Nat.add_div, Nat.reduceDiv, add_zero, Nat.mod_succ, Nat.reduceAdd, Std.le_refl, ↓reduceIte,
        mul_ite, mul_one, mul_zero, Finset.mem_Ico, Order.add_one_le_iff, Order.lt_add_one_iff,
        tsub_le_iff_right, and_imp]
        exact fun a ha₁ ha₂ => ⟨ Nat.sub_pos_of_lt ha₂, by omega ⟩
      · grind
      · simp +zetaDelta only [mul_ite, mul_one, mul_zero, Finset.mem_Ico, exists_prop,
        and_imp] at *
        exact fun b hb₁ hb₂ => ⟨ p - b, ⟨ by omega, by omega ⟩, by omega ⟩
      · intro k hk; rw [ Nat.cast_sub ( by linarith [ Finset.mem_Ico.mp hk ] ) ] ; ring_nf
    -- Notice that $\cos\left(\frac{2\pi (p - k) (x - r)}{p}\right) +
    -- \cos\left(\frac{2\pi (p - k) (x + r)}{p}\right) =
    -- \cos\left(\frac{2\pi k (x - r)}{p}\right) + \cos\left(\frac{2\pi k (x + r)}{p}\right)$.
    have h_cos_symm : ∀ k ∈ Finset.Ico 1 ((p + 1) / 2),
        Real.cos (2 * Real.pi * (p - k) * (x - r) / p) +
        Real.cos (2 * Real.pi * (p - k) * (x + r) / p) =
        Real.cos (2 * Real.pi * k * (x - r) / p) + Real.cos (2 * Real.pi * k * (x + r) / p) := by
      intro k hk; ring_nf
      norm_num [ mul_assoc, mul_comm Real.pi _, hp.ne_zero ]
      norm_num [ mul_assoc, mul_left_comm, hp.ne_zero ]
      norm_num [ Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub ] ; ring_nf
      norm_num [ mul_two, Real.sin_add, Real.cos_add ]
      norm_num [ show Real.sin ( Real.pi * r ) = 0 from Real.sin_eq_zero_iff.mpr ⟨ r, by
        push_cast ; ring ⟩ ]
    rw [ h_split, h_symm, Finset.sum_congr rfl h_cos_symm ] ; ring
  convert congr_arg ( fun y : ℝ => y / p ) h_sum.symm using 1
  · split_ifs
    · simp_all +decide only [← ZMod.natCast_eq_natCast_iff,
      Nat.cast_sub (show r ≤ p from Nat.div_le_of_le_mul <| by linarith), CharP.cast_eq_zero,
      zero_sub, ↓reduceIte, mul_one]
      rw [ div_self ( Nat.cast_ne_zero.mpr hp.ne_zero ) ]
    ·  simp_all +decide [ ← ZMod.natCast_eq_natCast_iff,
        Nat.cast_sub ( show r ≤ p from Nat.div_le_of_le_mul <| by linarith ) ]
    ·  simp_all +decide [ ← ZMod.natCast_eq_natCast_iff,
        Nat.cast_sub ( show r ≤ p from Nat.div_le_of_le_mul <| by linarith ) ]
    ·  simp_all +decide [ ← ZMod.natCast_eq_natCast_iff,
        Nat.cast_sub ( show r ≤ p from Nat.div_le_of_le_mul <| by linarith ) ]
  · rw [ h_split ] ; ring_nf
    norm_num [ Real.cos_add ] ; ring_nf
    norm_num [ ← Finset.sum_mul _ _ _ ] ; ring

/-- The Fourier expansion of g n i x. -/
lemma g_fourier_expansion (n : ℕ) (i : Fin (w n)) (x : ℕ) :
    g n i (x : ZMod (q n)) =
      2 / (p n i : ℝ) +
      (4 / (p n i : ℝ)) * ∑ k ∈ Finset.Ico 1 (((p n i) + 1) / 2),
        Real.cos (2 * Real.pi * (k : ℝ) * (krafftResidue n i : ℝ) / (p n i : ℝ)) *
        Real.cos (2 * Real.pi * (k : ℝ) * (x : ℝ) / (p n i : ℝ)) := by
  unfold g
  rw [show ((x : ZMod (q n)).cast : ZMod (p n i)) = (x : ZMod (p n i)) by
    rw [ZMod.cast_natCast (p_dvd_q n i)]]
  unfold krafftResidue
  exact krafft_pair_fourier (p n i) x (p_prime n i) (p_ge_5 n i)

/-- The DC component cancellation identity for g_i(x) * (1 + cos(theta))^2. -/
lemma dc_component_cancellation (p : ℝ) :
    3 / p - 4 / p * Real.cos (Real.pi / p) + 1 / p * Real.cos (2 * Real.pi / p) =
    (2 / p) * (1 - Real.cos (Real.pi / p))^2 := by
  have h_cos_2 : Real.cos (2 * Real.pi / p) = 2 * Real.cos (Real.pi / p)^2 - 1 := by
    have : 2 * Real.pi / p = 2 * (Real.pi / p) := by ring
    rw [this, Real.cos_two_mul]
  rw [h_cos_2]
  calc
    3 / p - 4 / p * Real.cos (Real.pi / p) + 1 / p * (2 * Real.cos (Real.pi / p)^2 - 1)
      = 3 / p - 4 / p * Real.cos (Real.pi / p) + 2 / p * Real.cos (Real.pi / p)^2 - 1 / p := by ring
    _ = 2 / p - 4 / p * Real.cos (Real.pi / p) + 2 / p * Real.cos (Real.pi / p)^2 := by ring
    _ = (2 / p) * (1 - 2 * Real.cos (Real.pi / p) + Real.cos (Real.pi / p)^2) := by ring
    _ = (2 / p) * (1 - Real.cos (Real.pi / p))^2 := by ring

/-- Reduction modulo `q n` does not change a basis cosine, since every `p n i`
divides `q n`. -/
lemma basis_cos_natCast_eq (n x : ℕ) (i : Fin (w n)) :
    Real.cos (2 * Real.pi * 3 * (((x : ZMod (q n)).val : ℝ)) / (p n i : ℝ)) =
      Real.cos (6 * Real.pi * (x : ℝ) / (p n i : ℝ)) := by
  rw [ZMod.val_natCast]
  have hp : p n i ∣ q n := p_dvd_q n i
  have hq : (q n : ℝ) = (p n i : ℝ) * (q n / p n i : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hp).symm
  have hx : (x : ℝ) = (x % q n : ℕ) + (q n : ℝ) * (x / q n : ℕ) := by
    exact_mod_cast (Nat.mod_add_div x (q n)).symm
  have heq : 6 * Real.pi * (x : ℝ) / (p n i : ℝ) =
      2 * Real.pi * 3 * (x % q n : ℕ) / (p n i : ℝ) +
        (((q n / p n i) * (x / q n) * 3 : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [hx, hq]
    push_cast
    field_simp [p_ne_zero n i]
    ring
  rw [heq]
  symm
  exact Real.cos_add_int_mul_two_pi _ _

/--
The continuous phase associated with a subset of primes.
This is the dominant frequency component in the Dirichlet expansion.
-/
noncomputable def subsetPhase (n : ℕ) (S : Finset (Fin (w n))) : ℝ :=
  ∑ i ∈ S, (p n i : ℝ)⁻¹

/--
A target interval for the phase that guarantees both positive mass and negative penalty.
These bounds rely on the valley of c(x) and the Dirichlet kernel evaluated at the center
of the Sieve interval.
-/
def isGoodPhaseInterval (n : ℕ) (a b : ℝ) : Prop :=
  a < b ∧
  ∀ S T : Finset (Fin (w n)), Disjoint S T →
    (subsetPhase n S + subsetPhase n T) ∈ Set.Icc a b →
    isRidge n S T ∧ penaltyMatrixEntry n S T ≤ 0

/--
Greedy Sequence Accumulation:
Given a sequence of positive reals that diverges to infinity and decays to 0, we can
always find a finite subset of disjoint indices whose sum falls into any target interval [a, b],
provided we start with an index sufficiently large such that the step size is smaller than b - a.
-/
lemma exists_subset_sum_in_interval {ι : Type*} (seq : ι → ℝ) (available : Finset ι)
    (a b : ℝ) (hab : a < b)
    (h_pos : ∀ i ∈ available, 0 < seq i)
    (h_step : ∀ i ∈ available, seq i < b - a)
    (h_mass : ∑ i ∈ available, seq i > b) :
    ∃ S ⊆ available, ∑ i ∈ S, seq i ∈ Set.Icc a b := by
  sorry

/--
The Halved Target Strategy:
If every individual vertex has its phase in [a/2, b/2], then every pairwise sum
is in [a, b], guaranteeing they all perfectly phase-lock into a clique.
-/
lemma ridge_clique_of_halved_phases (n : ℕ) (M : ℕ) (a b : ℝ) (hab : a < b)
    (h_good : isGoodPhaseInterval n a b)
    (vertices : Fin M → Finset (Fin (w n)))
    (h_disj : ∀ i j, i ≠ j → Disjoint (vertices i) (vertices j))
    (h_phases : ∀ i, subsetPhase n (vertices i) ∈ Set.Icc (a / 2) (b / 2)) :
    (ridgeGraph n).IsClique (Set.range vertices) ∧
    (∀ S ∈ Set.range vertices, ∀ T ∈ Set.range vertices, S ≠ T → penaltyMatrixEntry n S T ≤ 0) := by
  sorry

/--
Phase 6 Main Theorem: For sufficiently large n, there exists a large clique in the Ridge Graph
whose off-diagonal penalties are non-positive.
-/
theorem exists_large_ridge_clique (n : ℕ) (hn : 1000 ≤ n) :
    ∃ C : Finset (Finset (Fin (w n))),
      (ridgeGraph n).IsClique (C : Set (Finset (Fin (w n)))) ∧
      (∀ S ∈ C, ∀ T ∈ C, S ≠ T → penaltyMatrixEntry n S T ≤ 0) ∧
      (C.card : ℝ) >
        1 + 2 * (∑ x ∈ evalInterval n, c n (x : ZMod (q n))) / (evalInterval n).card := by
  -- 1. Identify the good phase interval [a, b] for this n.
  -- 2. Use exists_subset_sum_in_interval M times repeatedly to pluck out disjoint vertices.
  -- 3. Apply ridge_clique_of_halved_phases to conclude the clique properties.
  sorry

/-
A finite cosine sum over a natural interval satisfies the standard Dirichlet bound.
-/
lemma cosine_Icc_dirichlet_bound (A B : ℕ) (θ : ℝ)
    (h_not_int : ∀ k : ℤ, θ ≠ k) :
    |∑ x ∈ Finset.Icc A B, Real.cos (2 * Real.pi * θ * (x : ℝ))| ≤
      1 / |Real.sin (Real.pi * θ)| := by
  by_cases hB : B < A
  · rw [ Finset.Icc_eq_empty ] <;> norm_num ; linarith
  · -- Use the formula for the sum of a geometric series.
    have h_geo_series : ∑ x ∈ Finset.Icc A B, Complex.exp (2 * Real.pi * θ * x * Complex.I) =
        Complex.exp (2 * Real.pi * θ * A * Complex.I) *
        (1 - Complex.exp (2 * Real.pi * θ * (B - A + 1) * Complex.I)) /
        (1 - Complex.exp (2 * Real.pi * θ * Complex.I)) := by
      rw [ eq_div_iff ]
      · erw [ Finset.sum_Ico_eq_sum_range ]
        convert Finset.sum_range_sub'
            ( fun x => Complex.exp ( 2 * Real.pi * θ * ( A + x ) * Complex.I ) )
            ( B + 1 - A ) using 1 <;> norm_num [ Complex.exp_add, mul_add, add_mul,
              Finset.sum_range_succ ]
        · ring_nf
          simp +decide only [mul_comm, mul_assoc, Finset.mul_sum _ _ _, mul_left_comm]
        · rw [ Nat.cast_sub ( by linarith ) ] ; push_cast ; rw [ ← Complex.exp_add ] ; ring_nf
      · norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ]
        contrapose! h_not_int
        rw [ sub_eq_zero, eq_comm, Real.cos_eq_one_iff ] at h_not_int
        obtain ⟨ k, hk ⟩ := h_not_int.1; exact ⟨ k, by nlinarith [ Real.pi_pos ] ⟩
    -- Use the fact that $|1 - e^{i\phi}| = 2|\sin(\phi/2)|$ to simplify the expression.
    have h_abs : Complex.normSq (1 - Complex.exp (2 * Real.pi * θ * (B - A + 1) * Complex.I)) ≤
        4 ∧ Complex.normSq (1 - Complex.exp (2 * Real.pi * θ * Complex.I)) =
        4 * Real.sin (Real.pi * θ) ^ 2 := by
      norm_num [ Complex.normSq, Complex.exp_re, Complex.exp_im ]
      exact ⟨ by nlinarith only [ Real.cos_sq' ( 2 * Real.pi * θ * ( B - A + 1 ) ) ], by
        rw [ show 2 * Real.pi * θ = 2 * ( Real.pi * θ ) by ring,
             Real.sin_two_mul, Real.cos_two_mul ]
        nlinarith only [ Real.sin_sq_add_cos_sq ( Real.pi * θ ) ] ⟩
    -- Use the fact that $|e^{i\phi}| = 1$ to simplify the expression.
    have h_abs_exp : Complex.normSq
      (∑ x ∈ Finset.Icc A B, Complex.exp (2 * Real.pi * θ * x * Complex.I)) ≤
      4 / (4 * Real.sin (Real.pi * θ) ^ 2) := by
      rw [ h_geo_series, Complex.normSq_div ]
      rw [ Complex.normSq_mul, Complex.normSq_eq_norm_sq, Complex.norm_exp ]
      norm_num [ h_abs ]
      gcongr ; aesop
    rw [ ← Real.sqrt_sq_eq_abs ]
    rw [ Real.sqrt_le_left ] <;> norm_num [ Complex.normSq, Complex.exp_re, Complex.exp_im ] at *
    ring_nf at *; nlinarith

/-- The standard Dirichlet kernel bound for the sum of cosines over an interval.
    This shows that the oscillatory components grow at most as O(1/θ). -/
lemma dirichlet_kernel_bound (A B : ℕ) (θ : ℝ) (h_not_int : ∀ k : ℤ, θ ≠ k) :
    |∑ x ∈ Finset.Icc A B, Real.cos (2 * Real.pi * θ * (x : ℝ))| ≤
    1 / |Real.sin (Real.pi * θ)| :=
  cosine_Icc_dirichlet_bound A B θ h_not_int

/-- The largest prime used in the Krafft Sieve is bounded by O(log n).
    This guarantees that the minimum frequency θ >= 1 / p_w is large enough
    that the Dirichlet kernel bound is O(log n). -/
lemma max_prime_bound (n : ℕ) (h_large : 1000 ≤ n) :
    ∃ C > 0, ∀ i : Fin (w n), (p n i : ℝ) ≤ C * Real.log (n : ℝ) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 1000) h_large)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  let C : ℝ := (6 * n + 2 : ℕ) / Real.log (n : ℝ)
  refine ⟨C, div_pos (by positivity) hlog, fun i => ?_⟩
  rw [div_mul_cancel₀ _ hlog.ne']
  exact_mod_cast (le_of_lt (p_lt_range n i))

lemma one_add_cos_sq_expand (y : ℝ) :
    (1 + Real.cos y)^2 = 3/2 + 2 * Real.cos y + 1/2 * Real.cos (2 * y) := by
  have h_cos_sq : Real.cos y ^ 2 = (1 + Real.cos (2 * y)) / 2 := by
    linarith [Real.cos_sq y, Real.cos_two_mul y]
  calc
    (1 + Real.cos y)^2 = 1 + 2 * Real.cos y + Real.cos y ^ 2 := by ring
    _ = 1 + 2 * Real.cos y + (1 + Real.cos (2 * y)) / 2 := by rw [h_cos_sq]
    _ = 3/2 + 2 * Real.cos y + 1/2 * Real.cos (2 * y) := by ring

lemma one_add_cos_sq_expand' (y : ℝ) :
    1 + Real.cos y ^ 2 = 3/2 + 1/2 * Real.cos (2 * y) := by
  have h_cos_sq : Real.cos y ^ 2 = (1 + Real.cos (2 * y)) / 2 := by
    linarith [Real.cos_sq y, Real.cos_two_mul y]
  calc
    1 + Real.cos y ^ 2 = 1 + (1 + Real.cos (2 * y)) / 2 := by rw [h_cos_sq]
    _ = 3/2 + 1/2 * Real.cos (2 * y) := by ring

end KrafftSieve
