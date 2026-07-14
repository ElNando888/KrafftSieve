/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/
import Mathlib

/-!
# Auxiliary self-contained lemmas for the Gibbs dip (`GibbsDip.lean`)

This file collects the purely analytic / number-theoretic facts needed for the Gibbs
undershoot argument, stated without reference to the `KrafftSieve` RKHS machinery so that
they are reusable and self-contained.

* `cos_kernel_telescope` — the (multiplicative form of the) Dirichlet cosine kernel identity.
* `undershoot_value` — the Gibbs undershoot: the truncated cosine series of the symmetric
  step function dips below `-0.2` at the half-integer aligned with the residue.
* `exists_crt` — the Chinese Remainder Theorem: existence of a simultaneous solution.
* `sum_valley` — assembling the per-prime undershoots into the global continuous penalty bound.
-/

namespace KrafftSieve.GibbsAux

open scoped Real
open Finset

/-
**Dirichlet cosine kernel (telescoping form).**
For every real `θ` and `M : ℕ`,
`2 sin(θ/2) · ∑_{k=0}^{M} cos(kθ) = sin((M + 1/2)θ) + sin(θ/2)`.
This avoids any nonvanishing hypothesis on `sin(θ/2)`.
-/
lemma cos_kernel_telescope (θ : ℝ) (M : ℕ) :
    2 * Real.sin (θ / 2) * ∑ k ∈ Finset.range (M + 1), Real.cos (k * θ)
      = Real.sin (((M : ℝ) + 1 / 2) * θ) + Real.sin (θ / 2) := by
  induction' M with M ih <;> simp_all +decide [ Finset.sum_range_succ ];
  · ring;
  · convert congr_arg ( · + 2 * Real.sin ( θ / 2 ) * Real.cos ( ( M + 1 ) * θ ) ) ih using 1 ; ring;
    rw [ show ( M + 1 + 2⁻¹ : ℝ ) * θ = ( M + 1 ) * θ + θ / 2 by ring, show ( M + 2⁻¹ : ℝ ) * θ = ( M + 1 ) * θ - θ / 2 by ring ] ; rw [ Real.sin_add, Real.sin_sub ] ; ring;

/-
**Closed form of the Gibbs partial sum at the aligned half-integer.**
Under the residue alignment `Y ≡ R + 1 (mod P)` (with `P` an odd prime `≥ 5` and `R = (P+1)/6`),
the truncated symmetric cosine series collapses (via the Dirichlet kernel) to a sum of two
reciprocal-sine terms.
-/
set_option maxHeartbeats 4000000 in
theorem undershoot_closed_form (P R : ℕ) (hP : P.Prime) (hP5 : 5 ≤ P) (hR : R = (P + 1) / 6)
    (Y : ℤ) (hY : Y ≡ (R : ℤ) + 1 [ZMOD (P : ℤ)]) :
    ∑ k ∈ Finset.range ((P + 1) / 2),
        (if k = 0 then 2 / (P : ℝ)
          else if k ≤ (P - 1) / 2 then 4 / (P : ℝ) * Real.cos (2 * Real.pi * k * (R : ℝ) / (P : ℝ))
          else 0)
          * Real.cos (2 * Real.pi * k * ((Y : ℝ) + 0.5) / (P : ℝ))
      = -(1 / (P : ℝ)) * (1 / Real.sin (3 * Real.pi / (2 * P))
          + 1 / Real.sin ((4 * R + 3) * Real.pi / (2 * P))) := by
  -- Let's simplify the expression using the fact that $Y \equiv R + 1 \pmod{P}$.
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Y = R + 1 + P * m := by
    exact hY.symm.dvd.imp fun m hm => by linarith;
  -- Let's simplify the expression using the fact that $P$ is odd and $R = (P + 1) / 6$.
  have h_simp : ∑ k ∈ Finset.range ((P + 1) / 2), (if k = 0 then 2 / (P : ℝ) else if k ≤ (P - 1) / 2 then 4 / (P : ℝ) * Real.cos (2 * Real.pi * k * R / P) else 0) * Real.cos (2 * Real.pi * k * (R + 1.5) / P) = -(1 / (P : ℝ)) * (1 / Real.sin (3 * Real.pi / (2 * P)) + 1 / Real.sin ((4 * R + 3) * Real.pi / (2 * P))) := by
    -- Let's simplify the expression using the fact that $P$ is odd and $R = (P + 1) / 6$. We'll use the Dirichlet kernel identity.
    have h_dirichlet : ∑ k ∈ Finset.range ((P + 1) / 2), (if k = 0 then 2 / (P : ℝ) else if k ≤ (P - 1) / 2 then 4 / (P : ℝ) * Real.cos (2 * Real.pi * k * R / P) else 0) * Real.cos (2 * Real.pi * k * (R + 1.5) / P) = 2 / (P : ℝ) + (2 / (P : ℝ)) * (∑ k ∈ Finset.range ((P - 1) / 2), (Real.cos (2 * Real.pi * (k + 1) * (1.5) / P) + Real.cos (2 * Real.pi * (k + 1) * (2 * R + 1.5) / P))) := by
      have h_split : ∑ k ∈ Finset.range ((P + 1) / 2), (if k = 0 then 2 / (P : ℝ) else if k ≤ (P - 1) / 2 then 4 / (P : ℝ) * Real.cos (2 * Real.pi * k * R / P) else 0) * Real.cos (2 * Real.pi * k * (R + 1.5) / P) = 2 / (P : ℝ) + ∑ k ∈ Finset.range ((P - 1) / 2), (4 / (P : ℝ) * Real.cos (2 * Real.pi * (k + 1) * R / P) * Real.cos (2 * Real.pi * (k + 1) * (R + 1.5) / P)) := by
        rcases Nat.even_or_odd' P with ⟨ c, rfl | rfl ⟩ <;> norm_num at *;
        · simp_all +decide [ Nat.prime_mul_iff ];
        · norm_num [ Nat.add_div, Finset.sum_range_succ' ];
          rw [ add_comm, Finset.sum_congr rfl fun x hx => if_pos <| Finset.mem_range.mp hx ];
      rw [ h_split, Finset.mul_sum _ _ _ ];
      refine' congr rfl ( Finset.sum_congr rfl fun i hi => _ ) ; rw [ Real.cos_add_cos ] ; ring;
      norm_num [ Real.cos_add, Real.cos_sub ] ; ring;
    -- Let's simplify the expression using the fact that $P$ is odd and $R = (P + 1) / 6$. We'll use the Dirichlet kernel identity to simplify the sums.
    have h_dirichlet_simplified : ∑ k ∈ Finset.range ((P - 1) / 2), Real.cos (2 * Real.pi * (k + 1) * (1.5) / P) = (Real.sin ((P - 1) / 2 * (3 * Real.pi / P) + 3 * Real.pi / (2 * P)) - Real.sin (3 * Real.pi / (2 * P))) / (2 * Real.sin (3 * Real.pi / (2 * P))) := by
      have h_dirichlet_simplified : ∀ n : ℕ, ∑ k ∈ Finset.range n, Real.cos (2 * Real.pi * (k + 1) * (1.5) / P) = (Real.sin (n * (3 * Real.pi / P) + 3 * Real.pi / (2 * P)) - Real.sin (3 * Real.pi / (2 * P))) / (2 * Real.sin (3 * Real.pi / (2 * P))) := by
        intro n; rw [ eq_div_iff ] ; induction n <;> simp_all +decide [ Finset.sum_range_succ, add_mul ] ; ring;
        · rw [ ← Complex.ofReal_inj ] ; norm_num [ Complex.sin, Complex.cos ] ; ring;
          norm_num [ mul_assoc, ← Complex.exp_add ] ; ring;
        · exact mul_ne_zero two_ne_zero ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, show ( P : ℝ ) ≥ 5 by norm_cast ] ) ) );
      cases Nat.Prime.odd_of_ne_two hP ( by linarith ) ; aesop;
    have h_dirichlet_simplified2 : ∑ k ∈ Finset.range ((P - 1) / 2), Real.cos (2 * Real.pi * (k + 1) * (2 * R + 1.5) / P) = (Real.sin ((P - 1) / 2 * ((4 * R + 3) * Real.pi / P) + (4 * R + 3) * Real.pi / (2 * P)) - Real.sin ((4 * R + 3) * Real.pi / (2 * P))) / (2 * Real.sin ((4 * R + 3) * Real.pi / (2 * P))) := by
      have h_dirichlet_simplified2 : ∀ n : ℕ, ∑ k ∈ Finset.range n, Real.cos (2 * Real.pi * (k + 1) * (2 * R + 1.5) / P) = (Real.sin (n * ((4 * R + 3) * Real.pi / P) + (4 * R + 3) * Real.pi / (2 * P)) - Real.sin ((4 * R + 3) * Real.pi / (2 * P))) / (2 * Real.sin ((4 * R + 3) * Real.pi / (2 * P))) := by
        intro n;
        rw [ eq_div_iff ];
        · induction n <;> simp_all +decide [ Finset.sum_range_succ, add_mul ];
          rw [ ← Complex.ofReal_inj ] ; norm_num [ Complex.sin, Complex.cos ] ; ring;
          norm_num [ mul_assoc, ← Complex.exp_add ] ; ring;
        · norm_num [ Real.sin_eq_zero_iff ];
          intro x hx; rw [ eq_div_iff ( by positivity ) ] at hx; replace hx := congr_arg ( fun y => y / Real.pi ) hx; ring_nf at hx; norm_num [ Real.pi_ne_zero ] at hx;
          norm_num [ mul_assoc, mul_comm Real.pi _, Real.pi_ne_zero ] at hx;
          norm_cast at hx; have := congr_arg Even hx; norm_num [ parity_simps ] at this;
      convert h_dirichlet_simplified2 ( ( P - 1 ) / 2 ) using 2 ; rw [ Nat.cast_div ( show 2 ∣ P - 1 from even_iff_two_dvd.mp ( hP.even_sub_one <| by linarith ) ) ] <;> norm_num [ hP.pos ];
    rw [ h_dirichlet, Finset.sum_add_distrib, h_dirichlet_simplified, h_dirichlet_simplified2 ] ; ring;
    norm_num [ hP.ne_zero, mul_assoc, mul_comm Real.pi ] ; ring;
    rw [ show Real.pi * ( 3 / 2 ) = Real.pi / 2 + Real.pi by ring ] ; norm_num ; ring;
    rw [ mul_inv_cancel_right₀, mul_inv_cancel_right₀ ] <;> norm_num;
    · ring;
    · refine' ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi _ _ );
      · positivity;
      · field_simp;
        norm_cast ; omega;
    · exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by nlinarith [ Real.pi_pos, show ( P : ℝ ) ≥ 5 by norm_cast, inv_mul_cancel₀ ( by positivity : ( P : ℝ ) ≠ 0 ) ] ) );
  convert h_simp using 3 ; push_cast [ hm ] ; ring;
  convert Real.cos_periodic.int_mul ( m * ‹ℕ› ) _ using 2 ; push_cast ; ring_nf ; norm_num [ hP.ne_zero ];
  ring

/-
**The arithmetic bound.** The two-reciprocal-sine expression is `≤ -0.2`.
The first term alone already contributes at least `2/(3π) > 0.2` (since `sin θ ≤ θ`),
and the second term is nonnegative.
-/
theorem undershoot_bound (P R : ℕ) (hP5 : 5 ≤ P) (hR : R = (P + 1) / 6) :
    -(1 / (P : ℝ)) * (1 / Real.sin (3 * Real.pi / (2 * P))
        + 1 / Real.sin ((4 * R + 3) * Real.pi / (2 * P))) ≤ -(0.2 : ℝ) := by
  -- From `hR : R = (P+1)/6`, we have `6 * R ≤ P + 1` (nat division: `Nat.div_mul_le_self`/`Nat.mul_div_le`).
  -- Since `P ≥ 5`, `4 * R + 3 < 2 * P` (by linarith), which gives `b < π`. Hence `0 < Real.sin b` by `Real.sin_pos_of_pos_of_lt_pi`.
  have hb : (4 * R + 3) * Real.pi / (2 * P) < Real.pi := by
    rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( P : ℝ ) ≥ 5 by norm_cast, show ( R : ℝ ) ≤ ( P + 1 ) / 6 by exact hR.symm ▸ by rw [ le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self ( P + 1 ) 6 ] ]
  have hb_pos : 0 < Real.sin ((4 * R + 3) * Real.pi / (2 * P)) := by
    exact Real.sin_pos_of_pos_of_lt_pi ( by positivity ) hb;
  -- Since `sin a ≤ a` (by `Real.sin_lt`), `1 / sin a ≥ 1 / a`, so `(1/P) * (1/sin a + 1/sin b) ≥ (1/P) * (1/a)`.
  have h_bound : (1 / (P : ℝ)) * (1 / Real.sin (3 * Real.pi / (2 * P)) + 1 / Real.sin ((4 * R + 3) * Real.pi / (2 * P))) ≥ (1 / (P : ℝ)) * (1 / (3 * Real.pi / (2 * P))) := by
    gcongr;
    exact le_add_of_le_of_nonneg ( one_div_le_one_div_of_le ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, ( by norm_cast : ( 5 :ℝ ) ≤ P ) ] ) ) ( le_of_lt ( Real.sin_lt <| by positivity ) ) ) ( by positivity );
  -- Since `3 * π < 10`, we have `2 / (3 * π) > 0.2`.
  have h_pi_lt_315 : Real.pi < 3.15 := Real.pi_lt_d2
  ring_nf at *; norm_num at *;
  nlinarith [ Real.pi_gt_three, mul_inv_cancel₀ ( by positivity : ( P : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : Real.pi ≠ 0 ) ]

/-- **The Gibbs undershoot.**
Let `P` be a prime `≥ 5`, `R = (P+1)/6`, and let `Y` be an integer with `Y ≡ R + 1 (mod P)`.
The truncated symmetric cosine series (the Fourier partial sum of the local step function `g_i`),
evaluated at the half-integer `Y + 1/2`, is at most `-0.2`.

The coefficient expression is exactly `g_coef` inlined (`2/P` for `k = 0`,
`(4/P)·cos(2πkR/P)` for `1 ≤ k ≤ (P-1)/2`, and `0` otherwise). -/
theorem undershoot_value (P R : ℕ) (hP : P.Prime) (hP5 : 5 ≤ P) (hR : R = (P + 1) / 6)
    (Y : ℤ) (hY : Y ≡ (R : ℤ) + 1 [ZMOD (P : ℤ)]) :
    ∑ k ∈ Finset.range ((P + 1) / 2),
        (if k = 0 then 2 / (P : ℝ)
          else if k ≤ (P - 1) / 2 then 4 / (P : ℝ) * Real.cos (2 * Real.pi * k * (R : ℝ) / (P : ℝ))
          else 0)
          * Real.cos (2 * Real.pi * k * ((Y : ℝ) + 0.5) / (P : ℝ)) ≤ -(0.2 : ℝ) := by
  rw [undershoot_closed_form P R hP hP5 hR Y hY]
  exact undershoot_bound P R hP5 hR

/-
**Chinese Remainder Theorem (existence).**
Given pairwise coprime moduli `P i` (all nonzero) over a finite index type, and arbitrary
integer residues `A i`, there is an integer congruent to `A i` modulo `P i` for every `i`.
-/
theorem exists_crt {ι : Type*} [Fintype ι] (P : ι → ℕ) (A : ι → ℤ)
    (hP : ∀ i, P i ≠ 0) (hcop : ∀ i j, i ≠ j → Nat.Coprime (P i) (P j)) :
    ∃ Y : ℤ, ∀ i, Y ≡ A i [ZMOD (P i : ℤ)] := by
  -- Apply the Chinese Remainder Theorem to find such a `Y`.
  have h_crt : ∃ k : ℕ, ∀ i, k ≡ (A i % (P i : ℤ)).toNat [MOD (P i : ℕ)] := by
    have := @Nat.chineseRemainderOfFinset;
    specialize this ( fun i => ( A i % ( P i : ℤ ) |> Int.toNat ) ) ( fun i => P i ) Finset.univ ( fun i _ => hP i ) ( fun i _ j _ hij => hcop i j hij ) ; exact ⟨ this.1, fun i => this.2 i ( Finset.mem_univ i ) ⟩ ;
  obtain ⟨ k, hk ⟩ := h_crt; use k; intro i; specialize hk i; simp_all +decide [ ← Int.natCast_modEq_iff ] ;
  simp_all +decide [ Int.ModEq, Int.emod_nonneg _ ( Int.natCast_ne_zero.mpr ( hP i ) ) ]

/-
**Assembling the global penalty bound.**
If each modulus `P i` divides `Q` and each per-prime truncated series undershoots below `-0.2`
at `Y + 1/2`, then the sum over all primes, evaluated at the fractional part
`fract((Y + 1/2)/Q)` rescaled by `Q`, is at most `-0.2 · |ι|`.

The rescaling `fract(...) · Q` reproduces `Y + 1/2` modulo `P i` inside each cosine because
`P i ∣ Q`, so each inner sum equals the corresponding undershoot sum.
-/
theorem sum_valley {ι : Type*} [Fintype ι] (P : ι → ℕ) (Q : ℕ) (G : ι → ℕ → ℝ) (Y : ℤ)
    (hQ : 0 < Q) (hdvd : ∀ i, (P i) ∣ Q)
    (hunder : ∀ i, ∑ k ∈ Finset.range ((P i + 1) / 2),
        G i k * Real.cos (2 * Real.pi * k * ((Y : ℝ) + 0.5) / (P i : ℝ)) ≤ -(0.2 : ℝ)) :
    ∑ i : ι, ∑ k ∈ Finset.range ((P i + 1) / 2),
        G i k * Real.cos
          (2 * Real.pi * k * (Int.fract (((Y : ℝ) + 0.5) / (Q : ℝ))) * (Q : ℝ) / (P i : ℝ))
        ≤ -(0.2 : ℝ) * (Fintype.card ι) := by
  -- Apply the inequality from `hunder` to each term in the sum.
  have h_ineq : ∀ i : ι, ∑ k ∈ Finset.range ((P i + 1) / 2), G i k * Real.cos (2 * Real.pi * k * Int.fract ((Y + 0.5 : ℝ) / Q) * Q / (P i)) ≤ -0.2 := by
    intro i;
    convert hunder i using 3;
    rw [ Int.fract ];
    convert Real.cos_periodic.int_mul ( - ( ⌊ ( Y + 0.5 : ℝ ) / Q⌋ * ‹ℕ› * ( Q / P i ) ) ) _ using 2 ; push_cast ; ring;
    rw [ Int.cast_div ( mod_cast hdvd i ) ( by norm_cast; linarith [ Nat.pos_of_dvd_of_pos ( hdvd i ) hQ ] ) ] ; push_cast ; ring;
    simpa [ hQ.ne' ] using by ring;
  simpa [ mul_comm ] using Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => h_ineq i

/-!
### Quarter-integer variants

The lemmas above are stated at the half-integer offset `+0.5`. The `GibbsDip` argument instead
evaluates the truncated series at the *quarter-integer* offset `+0.25`. The closed form there is
`S = -(√2 / (2P)) · (1 / sin(5π/(4P)) + 1 / sin((8R+3)... ))`, and the resulting undershoot is
bounded above by `-0.1` (in fact by `-2√2/(5π) ≈ -0.18`).
-/

/-
**Closed form of the Gibbs partial sum at the aligned quarter-integer.**
Under `Y ≡ R + 1 (mod P)` with `P` an odd prime `≥ 5` and `R = (P+1)/6`, the truncated symmetric
cosine series evaluated at `Y + 1/4` collapses to a sum of two reciprocal-sine terms.
-/
theorem undershoot_closed_form_quarter (P R : ℕ) (hP : P.Prime) (hP5 : 5 ≤ P)
    (hR : R = (P + 1) / 6) (Y : ℤ) (hY : Y ≡ (R : ℤ) + 1 [ZMOD (P : ℤ)]) :
    ∑ k ∈ Finset.range ((P + 1) / 2),
        (if k = 0 then 2 / (P : ℝ)
          else if k ≤ (P - 1) / 2 then 4 / (P : ℝ) * Real.cos (2 * Real.pi * k * (R : ℝ) / (P : ℝ))
          else 0)
          * Real.cos (2 * Real.pi * k * ((Y : ℝ) + 0.25) / (P : ℝ))
      = -(Real.sqrt 2 / (2 * (P : ℝ))) * (1 / Real.sin (5 * Real.pi / (4 * P))
          + 1 / Real.sin ((8 * R + 5) * Real.pi / (4 * P))) := by
  -- Write Y as R + 1 + P * m for some integer m.
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Y = R + 1 + P * m := by
    exact hY.symm.dvd.imp fun m hm => by linarith;
  -- Expand the coefficient: pull out the k=0 term (2/P) and for 1 ≤ k ≤ (P-1)/2 use product-to-sum:
  have h_expand : ∑ k ∈ Finset.range ((P + 1) / 2), (if k = 0 then 2 / (P : ℝ) else if k ≤ (P - 1) / 2 then 4 / (P : ℝ) * Real.cos (2 * Real.pi * k * (R : ℝ) / (P : ℝ)) else 0) * Real.cos (2 * Real.pi * k * ((Y : ℝ) + 0.25) / (P : ℝ)) = (2 / (P : ℝ)) + (2 / (P : ℝ)) * ∑ k ∈ Finset.Ico 1 ((P + 1) / 2), (Real.cos (2 * Real.pi * k * (5 / 4 : ℝ) / (P : ℝ)) + Real.cos (2 * Real.pi * k * (2 * R + 5 / 4 : ℝ) / (P : ℝ))) := by
    have h_expand : ∀ k ∈ Finset.Ico 1 ((P + 1) / 2), (4 / (P : ℝ)) * Real.cos (2 * Real.pi * k * (R : ℝ) / (P : ℝ)) * Real.cos (2 * Real.pi * k * ((Y : ℝ) + 0.25) / (P : ℝ)) = (2 / (P : ℝ)) * (Real.cos (2 * Real.pi * k * (5 / 4 : ℝ) / (P : ℝ)) + Real.cos (2 * Real.pi * k * (2 * R + 5 / 4 : ℝ) / (P : ℝ))) := by
      intro k hk; rw [ Real.cos_add_cos ] ; ring; norm_num [ hm ] ; ring;
      norm_num [ hP.ne_zero ] ; ring; norm_num [ mul_assoc, mul_comm Real.pi ] ;
      exact Or.inl ( by convert Real.cos_periodic.int_mul ( k * m ) _ using 2; push_cast; ring );
    rw [ Finset.sum_eq_add_sum_sdiff_singleton_of_mem ( Finset.mem_range.mpr ( Nat.div_pos ( by linarith ) zero_lt_two ) ) ];
    rw [ Finset.mul_sum _ _ _ ];
    rw [ Finset.sdiff_singleton_eq_erase, Finset.range_eq_Ico ];
    rw [ Finset.Ico_eq_cons_Ioo, Finset.erase_cons ] <;> norm_num;
    · refine' Finset.sum_congr rfl fun x hx => _;
      grind;
    · linarith;
  -- Evaluate each Dirichlet cosine sum with the closed form Σ_{k=1}^{M} cos(kθ) = (sin((M+1/2)θ) − sin(θ/2))/(2 sin(θ/2)), with M=(P-1)/2.
  have h_dirichlet : ∀ θ : ℝ, Real.sin (θ / 2) ≠ 0 → ∑ k ∈ Finset.Ico 1 ((P + 1) / 2), Real.cos (k * θ) = (Real.sin ((P / 2) * θ) - Real.sin (θ / 2)) / (2 * Real.sin (θ / 2)) := by
    intro θ hθ
    have h_dirichlet_sum : ∑ k ∈ Finset.range ((P + 1) / 2), Real.cos (k * θ) = (Real.sin ((P / 2) * θ) + Real.sin (θ / 2)) / (2 * Real.sin (θ / 2)) := by
      have h_dirichlet_sum : ∀ n : ℕ, ∑ k ∈ Finset.range n, Real.cos (k * θ) = (Real.sin ((n - 1 / 2) * θ) + Real.sin (θ / 2)) / (2 * Real.sin (θ / 2)) := by
        intro n; rw [ eq_div_iff ( mul_ne_zero two_ne_zero hθ ) ] ; induction n <;> simp_all +decide [ Finset.sum_range_succ, add_mul ] ; ring;
        rw [ show ( ( _:ℝ ) + 1 - 2⁻¹ ) * θ = ( ( _:ℝ ) * θ ) + θ / 2 by ring ] ; rw [ show ( ( _:ℝ ) - 2⁻¹ ) * θ = ( ( _:ℝ ) * θ ) - θ / 2 by ring ] ; rw [ Real.sin_add, Real.sin_sub ] ; ring;
      convert h_dirichlet_sum ( ( P + 1 ) / 2 ) using 2 ; ring;
      rw [ Nat.cast_div ( show 2 ∣ 1 + P from even_iff_two_dvd.mp ( by simpa [ parity_simps ] using hP.eq_two_or_odd'.resolve_left ( by linarith ) ) ) ] <;> norm_num ; ring;
    rw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ h_dirichlet_sum ] ; ring;
    · grind;
    · omega;
  -- Apply the Dirichlet cosine sum formula to each term in the sum.
  have h_apply_dirichlet : ∑ k ∈ Finset.Ico 1 ((P + 1) / 2), Real.cos (2 * Real.pi * k * (5 / 4 : ℝ) / (P : ℝ)) = (Real.sin ((P / 2) * (5 * Real.pi / (2 * P))) - Real.sin (5 * Real.pi / (4 * P))) / (2 * Real.sin (5 * Real.pi / (4 * P))) ∧ ∑ k ∈ Finset.Ico 1 ((P + 1) / 2), Real.cos (2 * Real.pi * k * (2 * R + 5 / 4 : ℝ) / (P : ℝ)) = (Real.sin ((P / 2) * ((8 * R + 5) * Real.pi / (2 * P))) - Real.sin ((8 * R + 5) * Real.pi / (4 * P))) / (2 * Real.sin ((8 * R + 5) * Real.pi / (4 * P))) := by
    apply And.intro;
    · convert h_dirichlet ( 5 * Real.pi / ( 2 * P ) ) _ using 3 <;> ring;
      exact ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by nlinarith [ Real.pi_pos, show ( P : ℝ ) ≥ 5 by norm_cast, mul_inv_cancel₀ ( by positivity : ( P : ℝ ) ≠ 0 ) ] ) );
    · convert h_dirichlet ( ( 8 * R + 5 ) * Real.pi / ( 2 * P ) ) _ using 3 <;> ring;
      refine' ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi _ _ );
      · positivity;
      · field_simp;
        norm_cast ; linarith [ Nat.div_mul_le_self ( P + 1 ) 6 ];
  rw [ h_expand, Finset.sum_add_distrib, h_apply_dirichlet.1, h_apply_dirichlet.2 ]
  have hP0 : (P : ℝ) ≠ 0 := by positivity
  have hRle : (R : ℝ) ≤ ((P : ℝ) + 1) / 6 := by
    rw [le_div_iff₀ (by norm_num)]; norm_cast; nlinarith [Nat.div_mul_le_self (P + 1) 6, hR]
  have hs1 : Real.sin (5 * Real.pi / (4 * P)) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by positivity)
      (by rw [div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_pos, show (P : ℝ) ≥ 5 by norm_cast]))
  have hs2 : Real.sin ((8 * R + 5) * Real.pi / (4 * P)) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by positivity)
      (by rw [div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_pos, show (P : ℝ) ≥ 5 by norm_cast, hRle]))
  have e1 : ((P : ℝ) / 2) * (5 * Real.pi / (2 * P)) = 5 * Real.pi / 4 := by
    field_simp; ring
  have e2 : ((P : ℝ) / 2) * ((8 * R + 5) * Real.pi / (2 * P))
      = 5 * Real.pi / 4 + (R : ℝ) * (2 * Real.pi) := by
    field_simp; ring
  have s5 : Real.sin (5 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    rw [show (5 : ℝ) * Real.pi / 4 = Real.pi + Real.pi / 4 by ring, Real.sin_add]
    simp [Real.sin_pi_div_four, Real.cos_pi_div_four, Real.sin_pi, Real.cos_pi]
  rw [e1, e2, Real.sin_add_nat_mul_two_pi, s5]
  set s1 := Real.sin (5 * Real.pi / (4 * P)) with hs1def
  set s2 := Real.sin ((8 * R + 5) * Real.pi / (4 * P)) with hs2def
  field_simp
  ring

/-
**The arithmetic bound (quarter-integer).** The two-reciprocal-sine expression is `≤ -0.1`.
The first term alone contributes at least `2√2/(5π) > 0.1` (since `sin θ ≤ θ`), and the second
term is nonnegative because `(8R+5)π/(4P) < π` for `P ≥ 5`.
-/
theorem undershoot_bound_quarter (P R : ℕ) (hP5 : 5 ≤ P) (hR : R = (P + 1) / 6) :
    -(Real.sqrt 2 / (2 * (P : ℝ))) * (1 / Real.sin (5 * Real.pi / (4 * P))
        + 1 / Real.sin ((8 * R + 5) * Real.pi / (4 * P))) ≤ -(0.1 : ℝ) := by
  -- First, note that $b < \pi$ since $0 < \frac{(8R+5)\pi}{4P} < \pi$ for $P \geq 5$.
  have hb_lt_pi : (8 * R + 5) * Real.pi / (4 * P) < Real.pi := by
    rw [ div_lt_iff₀ ( by positivity ) ];
    nlinarith [ Real.pi_pos, show ( P : ℝ ) ≥ 5 by norm_cast, show ( R : ℝ ) ≤ ( P + 1 ) / 6 by rw [ le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self ( P + 1 ) 6 ] ];
  -- Next, show that $1/\sin b \geq 0$.
  have hb_pos : 0 < Real.sin ((8 * R + 5) * Real.pi / (4 * P)) := by
    exact Real.sin_pos_of_pos_of_lt_pi ( by positivity ) hb_lt_pi;
  -- Now use the fact that $1 / \sin a \geq 1 / a$ and $1 / \sin b \geq 0$ to bound the expression.
  have h_bound : 1 / Real.sin (5 * Real.pi / (4 * P)) + 1 / Real.sin ((8 * R + 5) * Real.pi / (4 * P)) ≥ 4 * P / (5 * Real.pi) := by
    refine' le_add_of_le_of_nonneg _ ( one_div_nonneg.mpr hb_pos.le );
    rw [ div_le_div_iff₀ ] <;> try positivity;
    · exact le_trans ( mul_le_mul_of_nonneg_left ( le_of_lt ( Real.sin_lt <| by positivity ) ) <| by positivity ) <| by nlinarith [ Real.pi_pos, show ( P : ℝ ) ≥ 5 by norm_cast, mul_div_cancel₀ ( 5 * Real.pi ) ( by positivity : ( 4 * P : ℝ ) ≠ 0 ) ] ;
    · exact Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, show ( P : ℝ ) ≥ 5 by norm_cast ] );
  refine' le_trans ( mul_le_mul_of_nonpos_left h_bound <| neg_nonpos_of_nonneg <| by positivity ) _;
  ring_nf; norm_num [ Real.pi_pos.ne', show P ≠ 0 by linarith ];
  rw [ ← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ ] <;> nlinarith only [ Real.pi_gt_three, Real.pi_le_four, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]

/-- **The Gibbs undershoot at the quarter-integer.**
Let `P` be a prime `≥ 5`, `R = (P+1)/6`, and let `Y` be an integer with `Y ≡ R + 1 (mod P)`.
The truncated symmetric cosine series (the Fourier partial sum of the local step function `g_i`),
evaluated at the quarter-integer `Y + 1/4`, is at most `-0.1`. -/
theorem undershoot_value_quarter (P R : ℕ) (hP : P.Prime) (hP5 : 5 ≤ P) (hR : R = (P + 1) / 6)
    (Y : ℤ) (hY : Y ≡ (R : ℤ) + 1 [ZMOD (P : ℤ)]) :
    ∑ k ∈ Finset.range ((P + 1) / 2),
        (if k = 0 then 2 / (P : ℝ)
          else if k ≤ (P - 1) / 2 then 4 / (P : ℝ) * Real.cos (2 * Real.pi * k * (R : ℝ) / (P : ℝ))
          else 0)
          * Real.cos (2 * Real.pi * k * ((Y : ℝ) + 0.25) / (P : ℝ)) ≤ -(0.1 : ℝ) := by
  rw [undershoot_closed_form_quarter P R hP hP5 hR Y hY]
  exact undershoot_bound_quarter P R hP5 hR

/-
**Assembling the global penalty bound (quarter-integer).**
If each modulus `P i` divides `Q` and each per-prime truncated series undershoots below `-0.1`
at `Y + 1/4`, then the sum over all primes, evaluated at the fractional part
`fract((Y + 1/4)/Q)` rescaled by `Q`, is at most `-0.1 · |ι|`.
-/
theorem sum_valley_quarter {ι : Type*} [Fintype ι] (P : ι → ℕ) (Q : ℕ) (G : ι → ℕ → ℝ) (Y : ℤ)
    (hQ : 0 < Q) (hdvd : ∀ i, (P i) ∣ Q)
    (hunder : ∀ i, ∑ k ∈ Finset.range ((P i + 1) / 2),
        G i k * Real.cos (2 * Real.pi * k * ((Y : ℝ) + 0.25) / (P i : ℝ)) ≤ -(0.1 : ℝ)) :
    ∑ i : ι, ∑ k ∈ Finset.range ((P i + 1) / 2),
        G i k * Real.cos
          (2 * Real.pi * k * (Int.fract (((Y : ℝ) + 0.25) / (Q : ℝ))) * (Q : ℝ) / (P i : ℝ))
        ≤ -(0.1 : ℝ) * (Fintype.card ι) := by
  have h_ineq : ∀ i : ι, ∑ k ∈ Finset.range ((P i + 1) / 2), G i k * Real.cos (2 * Real.pi * k * Int.fract ((Y + 0.25 : ℝ) / Q) * Q / (P i : ℝ)) ≤ -0.1 := by
    intro i
    convert hunder i using 3
    rw [Int.fract];
    convert Real.cos_periodic.int_mul ( -⌊ ( Y + 0.25 : ℝ ) / Q⌋ * ‹ℕ› * ( Q / P i ) ) _ using 2 ; push_cast ; ring;
    rw [ Int.cast_div ( mod_cast hdvd i ) ( by norm_cast; linarith [ Nat.pos_of_dvd_of_pos ( hdvd i ) hQ ] ) ] ; norm_num [ hQ.ne' ] ; ring;
  simpa [ mul_comm ] using Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => h_ineq i

end KrafftSieve.GibbsAux