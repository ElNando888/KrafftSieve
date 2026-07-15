import KrafftSieve.Discretization

namespace KrafftSieve

open scoped unitInterval
open unitInterval

/-- Removing the integral part in `rootPt` does not change a local cosine term,
because every local prime divides the global CRT period. -/
lemma rootPt_local_cos (n : ℕ) (i : Fin (w n)) (y : ℤ) (k : ℕ) :
    Real.cos (2 * Real.pi * k *
      ((((y : ℝ) + 0.25) / (q n : ℝ)) -
        ⌊(((y : ℝ) + 0.25) / (q n : ℝ))⌋) *
      (q n : ℝ) / (p n i : ℝ)) =
    Real.cos (2 * Real.pi * k * ((y : ℝ) + 0.25) / (p n i : ℝ)) := by
  convert Real.cos_periodic.int_mul
    (-⌊(((y : ℝ) + 0.25) / (q n : ℝ))⌋ * k * (q n / p n i)) _ using 2
  push_cast
  ring_nf
  rw [Int.cast_div (mod_cast p_dvd_q n i) (mod_cast p_ne_zero n i)]
  norm_num [p_ne_zero n i, NeZero.ne (q n)]
  ring

/-- A local Fourier interpolant only depends on the integer argument modulo its prime. -/
lemma local_eval_eq_of_modEq (n : ℕ) (i : Fin (w n)) (y z : ℤ)
    (h : y ≡ z [ZMOD (p n i : ℤ)]) :
    (∑ k ∈ Finset.range ((p n i + 1) / 2),
      g_coef n i k * Real.cos (2 * Real.pi * k * ((y : ℝ) + 0.25) / (p n i : ℝ))) =
    ∑ k ∈ Finset.range ((p n i + 1) / 2),
      g_coef n i k * Real.cos (2 * Real.pi * k * ((z : ℝ) + 0.25) / (p n i : ℝ)) := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, y = z + (p n i : ℤ) * m := by
    exact h.symm.dvd.imp fun m hm => by linarith
  refine Finset.sum_congr rfl fun k hk => ?_
  congr 1
  convert Real.cos_periodic.int_mul (k * m) _ using 2
  push_cast
  rw [hm]
  push_cast
  field_simp [p_ne_zero n i]
  ring

end KrafftSieve
