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

end KrafftSieve
