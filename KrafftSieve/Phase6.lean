import KrafftSieve.RidgeGraph
import KrafftSieve.OptimalWeights
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

/-- The Fourier expansion of g n i x. -/
lemma g_fourier_expansion (n : ℕ) (i : Fin (w n)) (x : ℕ) :
    g n i (x : ZMod (q n)) = 
      2 / (p n i : ℝ) + 
      (4 / (p n i : ℝ)) * ∑ k ∈ Finset.Ico 1 (((p n i) + 1) / 2),
        Real.cos (2 * Real.pi * (k : ℝ) * (krafftResidue n i : ℝ) / (p n i : ℝ)) * 
        Real.cos (2 * Real.pi * (k : ℝ) * (x : ℝ) / (p n i : ℝ)) := by
  sorry

noncomputable def totalPenalty (n : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin (w n))).powerset,
    ∑ T ∈ (Finset.univ : Finset (Fin (w n))).powerset,
      penaltyMatrixEntry n S T

noncomputable def totalDiagonalPenalty (n : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin (w n))).powerset,
    penaltyMatrixEntry n S S

noncomputable def totalOffDiagonalPenalty (n : ℕ) : ℝ :=
  totalPenalty n - totalDiagonalPenalty n

lemma totalOffDiagonalPenalty_eq (n : ℕ) :
    totalOffDiagonalPenalty n =
      ∑ x ∈ evalInterval n, c n (x : ZMod (q n)) *
        ((∏ j ∈ (Finset.univ : Finset (Fin (w n))),
          (1 + Real.cos (6 * Real.pi * (x : ℝ) / (p n j : ℝ))))^2 -
         (∏ j ∈ (Finset.univ : Finset (Fin (w n))),
           (1 + Real.cos (6 * Real.pi * (x : ℝ) / (p n j : ℝ))^2))) := by
  unfold totalOffDiagonalPenalty totalPenalty totalDiagonalPenalty penaltyMatrixEntry
  have h_sum_comm : ∑ S ∈ (Finset.univ : Finset (Fin (w n))).powerset,
                    ∑ T ∈ (Finset.univ : Finset (Fin (w n))).powerset,
                    ∑ x ∈ evalInterval n, c n (x : ZMod (q n)) *
                      basisFunction n S x * basisFunction n T x =
      ∑ x ∈ evalInterval n, c n (x : ZMod (q n)) *
        (∑ S ∈ (Finset.univ : Finset (Fin (w n))).powerset, basisFunction n S x) *
        (∑ T ∈ (Finset.univ : Finset (Fin (w n))).powerset, basisFunction n T x) := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    calc
      _ = ∑ S ∈ (Finset.univ : Finset (Fin (w n))).powerset,
            ∑ x ∈ evalInterval n,
              ∑ T ∈ (Finset.univ : Finset (Fin (w n))).powerset,
                c n (x : ZMod (q n)) * basisFunction n S x * basisFunction n T x := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [Finset.sum_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_comm]
  have h_diag_comm : ∑ S ∈ (Finset.univ : Finset (Fin (w n))).powerset,
      ∑ x ∈ evalInterval n, c n (x : ZMod (q n)) * basisFunction n S x * basisFunction n S x =
      ∑ x ∈ evalInterval n, c n (x : ZMod (q n)) *
        (∑ S ∈ (Finset.univ : Finset (Fin (w n))).powerset, basisFunction n S x ^ 2) := by
    simp_rw [pow_two, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [h_sum_comm, h_diag_comm]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have h_powerset : ∑ S ∈ (Finset.univ : Finset (Fin (w n))).powerset, basisFunction n S x =
      ∏ j ∈ (Finset.univ : Finset (Fin (w n))),
        (1 + Real.cos (6 * Real.pi * (x : ℝ) / (p n j : ℝ))) := by
    unfold basisFunction
    exact sum_powerset_prod_eq_prod_add_one Finset.univ _
  have h_powerset_sq : ∑ S ∈ (Finset.univ : Finset (Fin (w n))).powerset, basisFunction n S x ^ 2 =
      ∏ j ∈ (Finset.univ : Finset (Fin (w n))),
        (1 + Real.cos (6 * Real.pi * (x : ℝ) / (p n j : ℝ))^2) := by
    unfold basisFunction
    have : ∀ S ∈ (Finset.univ : Finset (Fin (w n))).powerset,
      (∏ j ∈ S, Real.cos (6 * Real.pi * (x : ℝ) / (p n j : ℝ))) ^ 2 =
        ∏ j ∈ S, Real.cos (6 * Real.pi * (x : ℝ) / (p n j : ℝ)) ^ 2 := fun S _ => by
          rw [← Finset.prod_pow]
    rw [Finset.sum_congr rfl this]
    exact sum_powerset_prod_eq_prod_add_one Finset.univ _
  rw [h_powerset, h_powerset_sq]
  ring

lemma totalOffDiagonalPenalty_decomp (n : ℕ) :
    totalOffDiagonalPenalty n = 
      ∑ i : Fin (w n), ∑ x ∈ evalInterval n, g n i (x : ZMod (q n)) * 
        ((∏ j ∈ (Finset.univ : Finset (Fin (w n))), (1 + Real.cos (6 * Real.pi * (x : ℝ) / (p n j : ℝ))))^2 - 
         (∏ j ∈ (Finset.univ : Finset (Fin (w n))), (1 + Real.cos (6 * Real.pi * (x : ℝ) / (p n j : ℝ))^2))) := by
  rw [totalOffDiagonalPenalty_eq]
  unfold c
  have : ∀ x ∈ evalInterval n, (∑ i : Fin (w n), g n i (x : ZMod (q n))) * 
        ((∏ j ∈ (Finset.univ : Finset (Fin (w n))), (1 + Real.cos (6 * Real.pi * (x : ℝ) / (p n j : ℝ))))^2 - 
         (∏ j ∈ (Finset.univ : Finset (Fin (w n))), (1 + Real.cos (6 * Real.pi * (x : ℝ) / (p n j : ℝ))^2))) =
        ∑ i : Fin (w n), g n i (x : ZMod (q n)) * 
        ((∏ j ∈ (Finset.univ : Finset (Fin (w n))), (1 + Real.cos (6 * Real.pi * (x : ℝ) / (p n j : ℝ))))^2 - 
         (∏ j ∈ (Finset.univ : Finset (Fin (w n))), (1 + Real.cos (6 * Real.pi * (x : ℝ) / (p n j : ℝ))^2))) := by
    intro x _
    exact Finset.sum_mul (Finset.univ : Finset (Fin (w n))) (fun i => g n i (x : ZMod (q n))) _
  rw [Finset.sum_congr rfl this]
  exact Finset.sum_comm

/-- The standard Dirichlet kernel bound for the sum of cosines over an interval. 
    This shows that the oscillatory components grow at most as O(1/θ). -/
lemma dirichlet_kernel_bound (A B : ℕ) (θ : ℝ) (h_not_int : ∀ k : ℤ, θ ≠ k) :
    |∑ x ∈ Finset.Icc A B, Real.cos (2 * Real.pi * θ * (x : ℝ))| ≤ 1 / |Real.sin (Real.pi * θ)| := by
  sorry

/-- The largest prime used in the Krafft Sieve is bounded by O(log n).
    This guarantees that the minimum frequency θ >= 1 / p_w is large enough
    that the Dirichlet kernel bound is O(log n). -/
lemma max_prime_bound (n : ℕ) (h_large : 1000 ≤ n) :
    ∃ C > 0, ∀ i : Fin (w n), (p n i : ℝ) ≤ C * Real.log (n : ℝ) := by
  sorry

/-- The oscillatory error terms are strictly bounded by O(log n), which is
    asymptotically crushed by the O(n) negative constant term. -/
lemma oscillatory_error_bound (n : ℕ) (h_large : 1000 ≤ n) :
    ∃ C > 0, |totalOffDiagonalPenalty n - 
      (- (∑ i : Fin (w n), 4 / (p n i : ℝ) * (3/2)^(w n - 1)) * ((evalInterval n).card : ℝ))| 
      ≤ C * Real.log (n : ℝ) := by
  sorry

/-- For sufficiently large n, the massive O(n) negative constant term dominates
    the O(log n) oscillatory errors, making the total off-diagonal penalty 
    strictly negative. -/
lemma totalOffDiagonalPenalty_neg_of_large_n {n : ℕ} (h_large : 1000 ≤ n) :
    totalOffDiagonalPenalty n < 0 := by
  sorry

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

/-- The strictly negative total off-diagonal penalty implies the existence
    of a clique C in the ridge graph of sufficient size to drive the 
    Rayleigh quotient strictly below 1, satisfying the requirements of
    `rayleigh_quotient_bound`. -/
lemma exists_large_clique_of_neg_penalty (n : ℕ) (h_large : 1000 ≤ n) :
    ∃ C : Finset (Finset (Fin (w n))),
      (ridgeGraph n).IsClique (C : Set (Finset (Fin (w n)))) ∧
      (C.card : ℝ) > 1 + 2 * (∑ x ∈ evalInterval n, c n (x : ZMod (q n))) / (evalInterval n).card := by
  sorry

end KrafftSieve
