/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela

Task 4: The Krafft Geometric Translation Theorem
Proves the rigid spatial vector for strikes from P_large.
For p > L, p strikes at most one element for S⁺ and at most one for S⁻.
The absolute modulo distance between these strikes is rigidly fixed by p's Krafft parameter.
-/

import Mathlib
import Legendre.SieveSplitting

open scoped BigOperators

set_option linter.style.setOption false
set_option linter.style.longLine false

noncomputable section

/-! ## Large prime single-strike property -/

/-
PROBLEM
For p > L = 2n, a single residue class mod p hits at most one element
    in any interval of length ≤ 2n.

PROVIDED SOLUTION
If a ≡ b (mod p) and both a, b are in Bk n k (an interval of length ≤ 2n), then |a - b| < 2n+1 ≤ p (since p > 2n). But a ≡ b (mod p) means p ∣ (a - b). Since |a - b| < p, we must have a - b = 0, so a = b.
-/
theorem large_prime_at_most_one_hit (n : ℕ) (p : ℕ) (hp : p > 2 * n)
    (a b : ℤ) (ha : a ∈ Bk n k) (hb : b ∈ Bk n k)
    (hab : a ≡ b [ZMOD (p : ℤ)]) : a = b := by
      -- Since a ≡ b mod p, we have p divides (a - b).
      have h_div : (p : ℤ) ∣ (a - b) := by
        exact hab.symm.dvd;
      obtain ⟨ x, hx ⟩ := h_div;
      -- Since $a$ and $b$ are in the interval $Bk n k$, we have $|a - b| \leq 2n$.
      have h_diff_le : |a - b| ≤ 2 * n := by
        fin_cases k <;> simp +decide [ Bk ] at ha hb ⊢ <;> rw [ abs_le ] <;> constructor <;> linarith! [ Finset.mem_Icc.mp ha, Finset.mem_Icc.mp hb ] ;
      nlinarith [ abs_le.mp h_diff_le, show x = 0 by nlinarith [ abs_le.mp h_diff_le ] ]

/-! ## Krafft geometric translation vector -/

/-
PROBLEM
The modular distance between the S⁺ and S⁻ hits for a prime p = 6m + α is
    Δ_p ≡ X_p⁺ - X_p⁻ ≡ 2αm (mod p).

PROVIDED SOLUTION
By definition, sieve_hit_plus p m alpha = (alpha * m : ℤ) and sieve_hit_minus p m alpha = (-alpha * m : ℤ). Their difference in ZMod p is (alpha * m - (-alpha * m) : ℤ) = (2 * alpha * m : ℤ). This is a direct computation in ZMod p using the definitions.
-/
theorem krafft_translation_vector (p : ℕ) (m : ℤ) (alpha : ℤ)
    (halpha : alpha = 1 ∨ alpha = -1) (hp_eq : (p : ℤ) = 6 * m + alpha) :
    (sieve_hit_plus p m alpha : ZMod p) - (sieve_hit_minus p m alpha : ZMod p) =
    ((2 * alpha * m : ℤ) : ZMod p) := by
      unfold sieve_hit_plus sieve_hit_minus; ring;
      norm_num [ mul_two ]

/-
PROBLEM
For large primes, p > L implies 2m ≈ p/3, so the translation vector
    spans roughly 1/3 of the modular period — a large rigid displacement.

PROVIDED SOLUTION
From p = 6m + α with α ∈ {1,-1}, we get m = (p - α)/6. So |m| = (p - α)/6 (m is positive since p ≥ 5). Then 2|m| = (p - α)/3 ≥ (p - 1)/3. Cases on alpha: if alpha=1, m = (p-1)/6, 2m = (p-1)/3 ≥ (p-1)/3. If alpha=-1, m = (p+1)/6, 2m = (p+1)/3 ≥ (p-1)/3.
-/
theorem krafft_parameter_bound (p : ℕ) (m : ℤ) (alpha : ℤ)
    (halpha : alpha = 1 ∨ alpha = -1) (hp_eq : (p : ℤ) = 6 * m + alpha)
    (hp5 : 5 ≤ p) :
    2 * |m| ≥ ((p : ℤ) - 1) / 3 := by
      cases' halpha with halpha halpha <;> cases abs_cases m <;> omega

/-! ## Paired strike constraint -/

/-
PROBLEM
If p ∈ P_large strikes x_plus via S⁺ and x_minus via S⁻ in interval B_n^(k),
    then x_plus and x_minus are separated by exactly 2αm mod p. Since p > 2n,
    this is an absolute (not modular) constraint within the interval.

PROVIDED SOLUTION
From p ∣ 6*x_plus+1 and p ∣ 6*x_minus-1, we get p ∣ (6*x_plus+1) - (6*x_minus-1) = 6*(x_plus - x_minus) + 2. Also p ∣ 6*(x_plus - x_minus) + 2. Since p = 6m+α, we need x_plus - x_minus ≡ 2αm (mod p). From p ∣ 6*x_plus+1, we get 6*x_plus ≡ -1 (mod p). From p ∣ 6*x_minus-1, we get 6*x_minus ≡ 1 (mod p). So 6*(x_plus - x_minus) ≡ -2 (mod p). Since p = 6m+α, 6 has an inverse mod p (as p ≥ 5 is prime, gcd(6,p)=1). We have x_plus - x_minus ≡ -2/6 (mod p). But 6*αm ≡ -α² = -1 (mod p), so 1/6 ≡ -αm (mod p), and -2/6 ≡ 2αm (mod p).
-/
theorem paired_strike_separation (n : ℕ) (k : Fin 6) (p : ℕ) (hp : p ∈ P_large n)
    (m : ℤ) (alpha : ℤ) (halpha : alpha = 1 ∨ alpha = -1)
    (hp_eq : (p : ℤ) = 6 * m + alpha) (hp_prime : Nat.Prime p)
    (x_plus x_minus : ℤ) (hxp : x_plus ∈ Bk n k) (hxm : x_minus ∈ Bk n k)
    (h_hit_plus : (p : ℤ) ∣ 6 * x_plus + 1) (h_hit_minus : (p : ℤ) ∣ 6 * x_minus - 1) :
    x_plus - x_minus ≡ 2 * alpha * m [ZMOD (p : ℤ)] := by
      -- From the divisibility conditions, we have $6x_plus ≡ -1 \pmod{p}$ and $6x_minus ≡ 1 \pmod{p}$.
      have h_mod_plus : (6 * x_plus : ℤ) ≡ -1 [ZMOD p] := by
        exact Eq.symm <| Int.modEq_of_dvd h_hit_plus
      have h_mod_minus : (6 * x_minus : ℤ) ≡ 1 [ZMOD p] := by
        exact Eq.symm <| Int.modEq_of_dvd h_hit_minus;
      -- From the divisibility conditions, we have $6(x_plus - x_minus) ≡ -2 \pmod{p}$.
      have h_mod_diff : (6 * (x_plus - x_minus) : ℤ) ≡ -2 [ZMOD p] := by
        simpa [ mul_sub ] using h_mod_plus.sub h_mod_minus;
      rw [ Int.modEq_iff_dvd ] at *;
      obtain h | h := halpha <;> simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ];
      · obtain ⟨ k, hk ⟩ := h_mod_diff;
        exact ⟨ -k * m - ( x_plus - x_minus ), by nlinarith ⟩;
      · obtain ⟨ k, hk ⟩ := h_mod_diff;
        exact ⟨ k * m + ( x_plus - x_minus ), by cases le_or_gt 0 m <;> nlinarith ⟩

end