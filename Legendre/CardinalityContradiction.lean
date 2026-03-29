/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela

Task 5: The Cardinality Contradiction (Wasted Cover)
Sets up the contradiction scaffold assuming a complete double cover,
and shows that P_large cannot perfectly exhaust U⁺ ∪ U⁻ due to geometric constraints,
yielding the existence of a survivor.
-/

import Mathlib
import Legendre.TuranBounds
import Legendre.GeometricTranslation
import KrafftSieve.Variance
import KrafftSieve.OptimalWeights

open scoped BigOperators

set_option linter.style.setOption false
set_option linter.style.longLine false

open Classical in
noncomputable section

/-! ## Double cover assumption and contradiction -/

/-- A "double cover" by P_large means: every element of U⁺ is hit by some large prime via S⁺,
    AND every element of U⁻ is hit by some large prime via S⁻. -/
def DoubleCover (n : ℕ) (k : Fin 6) : Prop :=
  (∀ x ∈ U_plus n k, ∃ p ∈ P_large n, (p : ℤ) ∣ (6 * x + 1)) ∧
  (∀ x ∈ U_minus n k, ∃ p ∈ P_large n, (p : ℤ) ∣ (6 * x - 1))

/-- Each large prime can cover at most 1 element of U⁺ (since p > L = 2n
    and the interval has length ≤ 2n + 1). -/
theorem large_prime_covers_at_most_one_plus (n : ℕ) (k : Fin 6) (p : ℕ)
    (hp : p ∈ P_large n) (hp_prime : Nat.Prime p) :
    ((U_plus n k).filter (fun x => (p : ℤ) ∣ (6 * x + 1))).card ≤ 1 := by
      have h_max_cover (p : ℕ) (hp : p ∈ P_large n) (hp_prime : Nat.Prime p) :
          ∀ x y : ℤ, x ∈ U_plus n k → y ∈ U_plus n k →
          (p : ℤ) ∣ 6 * x + 1 → (p : ℤ) ∣ 6 * y + 1 → x = y := by
        intros x y hx hy hpx hpy
        have h_div : (p : ℤ) ∣ (6 * (x - y)) := by convert dvd_sub hpx hpy using 1; ring
        have h_contra : (p : ℤ) ∣ (x - y) := by
          haveI := Fact.mk hp_prime; simp_all +decide [← ZMod.intCast_zmod_eq_zero_iff_dvd]; aesop
        exact large_prime_at_most_one_hit n p (P_large_gt_L n p hp) x y
          (U_plus_subset n k hx) (U_plus_subset n k hy) (Int.ModEq.symm <| Int.modEq_of_dvd h_contra)
      exact Finset.card_le_one.mpr fun x hx y hy =>
        h_max_cover p hp hp_prime x y (Finset.filter_subset _ _ hx) (Finset.filter_subset _ _ hy)
          (Finset.mem_filter.mp hx |>.2) (Finset.mem_filter.mp hy |>.2)

/-- Each large prime can cover at most 1 element of U⁻. -/
theorem large_prime_covers_at_most_one_minus (n : ℕ) (k : Fin 6) (p : ℕ)
    (hp : p ∈ P_large n) (hp_prime : Nat.Prime p) :
    ((U_minus n k).filter (fun x => (p : ℤ) ∣ (6 * x - 1))).card ≤ 1 := by
      have h_congr : ∀ x y : ℤ, x ∈ U_minus n k → y ∈ U_minus n k →
          (p : ℤ) ∣ (6 * x - 1) → (p : ℤ) ∣ (6 * y - 1) → x ≡ y [ZMOD p] := by
        intro x y hx hy hx' hy'
        have h_contra : (p : ℤ) ∣ (x - y) := by
          haveI := Fact.mk hp_prime; simp_all +decide [← ZMod.intCast_zmod_eq_zero_iff_dvd, sub_eq_iff_eq_add]; grind
        exact Eq.symm <| Int.modEq_of_dvd h_contra
      refine Finset.card_le_one_iff.mpr ?_
      norm_num +zetaDelta at *
      intro a b ha ha' hb hb'; specialize h_congr a b ha hb ha' hb'; rw [Int.ModEq] at h_congr
      exact large_prime_at_most_one_hit n p (P_large_gt_L n p hp) a b (U_minus_subset n k ha) (U_minus_subset n k hb) h_congr

/-- Under a double cover, |P_large| ≥ |U⁺|. -/
theorem cover_requires_enough_primes_plus (n : ℕ) (k : Fin 6)
    (h_cover : DoubleCover n k) :
    (U_plus n k).card ≤ (P_large n).card := by
      choose! f hf using h_cover.1
      have h_inj : ∀ x y : ℤ, x ∈ U_plus n k → y ∈ U_plus n k → x ≠ y → (f x : ℤ) ≠ (f y : ℤ) := by
        intros x y hx hy hxy h_eq
        have := large_prime_covers_at_most_one_plus n k (f x) (hf x hx |>.1) ?_ <;>
          simp_all +decide [Finset.card_le_one]
        · grind
        · exact Finset.mem_filter.mp (hf y hy |>.1) |>.2.2.2
      have h_card : Finset.card (Finset.image f (U_plus n k)) ≤ Finset.card (P_large n) :=
        Finset.card_le_card (Finset.image_subset_iff.mpr fun x hx => hf x hx |>.1)
      rwa [Finset.card_image_of_injOn fun x hx y hy hxy =>
        Classical.not_not.1 fun h => h_inj x y hx hy h (mod_cast hxy)] at h_card

/-- Under a double cover, |P_large| ≥ |U⁻|. -/
theorem cover_requires_enough_primes_minus (n : ℕ) (k : Fin 6)
    (h_cover : DoubleCover n k) :
    (U_minus n k).card ≤ (P_large n).card := by
      choose! f hf using h_cover.2
      have h_inj : ∀ x y : ℤ, x ∈ U_minus n k → y ∈ U_minus n k → f x = f y → x = y := by
        intros x y hx hy hxy
        have h_eq : (f x : ℤ) ∣ (6 * x - 1) ∧ (f x : ℤ) ∣ (6 * y - 1) := by grind +ring
        have := large_prime_covers_at_most_one_minus n k (f x) (hf x hx |>.1)
          (Nat.prime_iff.mpr <| Nat.prime_iff.mp (Finset.mem_filter.mp (hf x hx).1 |>.2.2.2))
        rw [Finset.card_le_one_iff] at this
        exact this (Finset.mem_filter.mpr ⟨hx, h_eq.1⟩) (Finset.mem_filter.mpr ⟨hy, h_eq.2⟩)
      have h_card : (U_minus n k).card ≤ (Finset.image f (U_minus n k)).card :=
        (Finset.card_image_of_injOn fun x hx y hy hxy => h_inj x y hx hy hxy).symm ▸ le_refl _
      exact h_card.trans (Finset.card_le_card <| Finset.image_subset_iff.mpr fun x hx => hf x hx |>.1)

/-! ## Wasted covering power -/

/-- The "wasted cover" principle: when a large prime p simultaneously hits x⁺ ∈ U⁺
    and x⁻ ∈ U⁻, the geometric constraint (separation ≡ 2αm mod p) means p's covering
    power is "wasted" — the pair (x⁺, x⁻) is rigidly linked, so p covers at most
    1 element of U⁺ ∪ U⁻ effectively (not 2 independent ones). -/
noncomputable def wasted_primes (n : ℕ) (k : Fin 6) : Finset ℕ :=
  (P_large n).filter (fun p =>
    (∃ x ∈ U_plus n k, (p : ℤ) ∣ (6 * x + 1)) ∧
    (∃ x ∈ U_minus n k, (p : ℤ) ∣ (6 * x - 1)))

/-
PROBLEM
The effective covering capacity: under a double cover, |U⁺| + |U⁻| ≤ |P_large| + |wasted|.
    This follows from inclusion-exclusion: the injective coverage maps f⁺ : U⁺ → P_large
    and f⁻ : U⁻ → P_large satisfy |im(f⁺) ∪ im(f⁻)| ≤ |P_large|, and
    im(f⁺) ∩ im(f⁻) ⊆ wasted_primes, so
    |U⁺| + |U⁻| = |im(f⁺)| + |im(f⁻)| = |im(f⁺) ∪ im(f⁻)| + |im(f⁺) ∩ im(f⁻)|
                 ≤ |P_large| + |wasted_primes|.

PROVIDED SOLUTION
Under the double cover, choose injective functions f⁺ : U_plus → P_large and f⁻ : U_minus → P_large (built from h_cover.1 and h_cover.2 respectively, with injectivity from the at-most-one-hit property).

Let A = im(f⁺) and B = im(f⁻). Then |A| = |U_plus|, |B| = |U_minus|.
By inclusion-exclusion: |A ∪ B| = |A| + |B| - |A ∩ B|.
Since A ∪ B ⊆ P_large: |A ∪ B| ≤ |P_large|.
Also A ∩ B ⊆ wasted_primes (any prime in both images hits both U+ and U-).
So: |U_plus| + |U_minus| - |A ∩ B| ≤ |P_large|, hence |U_plus| + |U_minus| ≤ |P_large| + |A ∩ B| ≤ |P_large| + |wasted_primes|.

Use `Finset.card_union_add_card_inter` for inclusion-exclusion.
-/
theorem effective_coverage_bound (n : ℕ) (k : Fin 6)
    (h_cover : DoubleCover n k) :
    (U_plus n k).card + (U_minus n k).card ≤
    (P_large n).card + (wasted_primes n k).card := by
      obtain ⟨f_plus, hf_plus⟩ : ∃ f_plus : ↥(U_plus n k) → ℕ, Function.Injective f_plus ∧ ∀ x : ↥(U_plus n k), f_plus x ∈ P_large n ∧ (f_plus x : ℤ) ∣ 6 * x.val + 1 := by
        have := h_cover.1;
        choose f hf₁ hf₂ using this;
        use fun x => f x x.2;
        refine' ⟨ _, fun x => ⟨ hf₁ _ _, hf₂ _ _ ⟩ ⟩;
        intro x y hxy;
        have := large_prime_covers_at_most_one_plus n k ( f x x.2 ) ( hf₁ x x.2 ) ( by
          exact Finset.mem_filter.mp ( hf₁ _ x.2 ) |>.2.2.2 );
        rw [ Finset.card_le_one_iff ] at this;
        exact Subtype.ext <| this ( Finset.mem_filter.mpr ⟨ x.2, hf₂ _ _ ⟩ ) ( Finset.mem_filter.mpr ⟨ y.2, by simpa [ hxy ] using hf₂ _ _ ⟩ );
      obtain ⟨f_minus, hf_minus⟩ : ∃ f_minus : ↥(U_minus n k) → ℕ, Function.Injective f_minus ∧ ∀ x : ↥(U_minus n k), f_minus x ∈ P_large n ∧ (f_minus x : ℤ) ∣ 6 * x.val - 1 := by
        choose! f_minus hf_minus using h_cover.2;
        refine' ⟨ _, _, _ ⟩;
        exact fun x => f_minus x.val;
        · intro x y hxy;
          have := large_prime_covers_at_most_one_minus n k ( f_minus x ) ( hf_minus x x.2 |>.1 ) ( by
            exact Finset.mem_filter.mp ( hf_minus x x.2 |>.1 ) |>.2.2.2 );
          rw [ Finset.card_le_one_iff ] at this;
          exact Subtype.ext <| this ( Finset.mem_filter.mpr ⟨ x.2, by simpa [ hxy ] using hf_minus x x.2 |>.2 ⟩ ) ( Finset.mem_filter.mpr ⟨ y.2, by simpa [ hxy ] using hf_minus y y.2 |>.2 ⟩ );
        · exact fun x => hf_minus _ x.2;
      have h_union_inter : (Finset.image f_plus Finset.univ ∪ Finset.image f_minus Finset.univ).card + (Finset.image f_plus Finset.univ ∩ Finset.image f_minus Finset.univ).card = (Finset.image f_plus Finset.univ).card + (Finset.image f_minus Finset.univ).card := by
        rw [ Finset.card_union_add_card_inter ];
      rw [ Finset.card_image_of_injective _ hf_plus.1, Finset.card_image_of_injective _ hf_minus.1 ] at h_union_inter;
      refine' le_trans _ ( add_le_add ( Finset.card_le_card <| show Finset.image f_plus Finset.univ ∪ Finset.image f_minus Finset.univ ⊆ P_large n from _ ) ( Finset.card_le_card <| show Finset.image f_plus Finset.univ ∩ Finset.image f_minus Finset.univ ⊆ wasted_primes n k from _ ) );
      · aesop;
      · exact Finset.union_subset ( Finset.image_subset_iff.mpr fun x _ => hf_plus.2 x |>.1 ) ( Finset.image_subset_iff.mpr fun x _ => hf_minus.2 x |>.1 );
      · simp_all +decide [ Finset.subset_iff ];
        intro p x hx hx' y hy hy'; subst_vars; simp_all +decide [ wasted_primes ] ;
        exact ⟨ ⟨ x, hx, hf_plus.2 x hx |>.2 ⟩, ⟨ y, hy, hy'.symm ▸ hf_minus.2 y hy |>.2 ⟩ ⟩

/-! ## Main contradiction scaffold -/

/-- The double cover contradiction: assuming sufficient density of survivors
    (|U⁺| + |U⁻| large enough relative to |P_large|), the double cover
    assumption leads to a contradiction, guaranteeing at least one survivor. -/
theorem double_cover_contradiction (n : ℕ) (hn : n ≥ 1) (k : Fin 6)
    (h_density : (U_plus n k).card + (U_minus n k).card >
                 (P_large n).card + (wasted_primes n k).card)
    (h_cover : DoubleCover n k) : False := by
  exact absurd (effective_coverage_bound n k h_cover) (not_le.mpr h_density)

/-
PROBLEM
Existence of a survivor: if the density condition holds,
    then there exists x in B_n^(k) that survives at least one of the two sieves
    against all sieving primes.

PROVIDED SOLUTION
By contraposition. Assume the negation: for every x ∈ Bk n k, there exists some prime p (5 ≤ p < 6n+2) with p ∣ 6x+1, AND there exists some prime q with q ∣ 6x-1.

Then in particular, every x ∈ U_plus n k (which are elements of Bk n k not hit by P_small via S+) must be hit by some prime via S+. Since it survived P_small, the prime must be in P_large. Similarly for U_minus. So the DoubleCover holds.

But then effective_coverage_bound gives |U+| + |U-| ≤ |P_large| + |wasted|, contradicting h_density.
-/
theorem survivor_exists (n : ℕ) (hn : n ≥ 1) (k : Fin 6)
    (h_density : (U_plus n k).card + (U_minus n k).card >
                 (P_large n).card + (wasted_primes n k).card) :
    (∃ x ∈ Bk n k, ∀ p : ℕ, p.Prime → 5 ≤ p → p < 6 * n + 2 →
      ¬((p : ℤ) ∣ (6 * x + 1))) ∨
    (∃ x ∈ Bk n k, ∀ p : ℕ, p.Prime → 5 ≤ p → p < 6 * n + 2 →
      ¬((p : ℤ) ∣ (6 * x - 1))) := by
        contrapose! h_density;
        apply_rules [ effective_coverage_bound ];
        constructor <;> intro x hx <;> rcases h_density.1 x ( Finset.mem_filter.mp hx |>.1 ) with ⟨ p, hp₁, hp₂, hp₃, hp₄ ⟩ <;> rcases h_density.2 x ( Finset.mem_filter.mp hx |>.1 ) with ⟨ q, hq₁, hq₂, hq₃, hq₄ ⟩;
        · by_cases hp : p ≤ 2 * n;
          · exact False.elim <| Finset.mem_filter.mp hx |>.2 p ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| by linarith, hp₂, hp₁ ⟩ ) hp₄;
          · exact ⟨ p, Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr hp₃, by linarith, by linarith, hp₁ ⟩, hp₄ ⟩;
        · by_cases hq₅ : q ≤ 2 * n;
          · exact False.elim <| Finset.mem_filter.mp hx |>.2 q ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| by linarith, by linarith, hq₁ ⟩ ) hq₄;
          · exact ⟨ q, Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr hq₃, by linarith, by linarith, hq₁ ⟩, hq₄ ⟩

/-! ## Task 8: Asymptotic Density Substitution -/

/-! ### Bridge: Surviving the sieve implies primality

The crucial observation: if x ∈ Bk n k and 6x+1 has no prime divisor p with 5 ≤ p < 6n+2,
then 6x+1 must be prime. The argument:

1. 6x+1 ≡ 1 mod 6, so it's not divisible by 2 or 3.
2. 6x+1 < (6n+k)² (from legendre_targeting).
3. If 6x+1 were composite with smallest prime factor q, then q² ≤ 6x+1 < (6n+k)²,
   so q < 6n+k ≤ 6n+5.
4. Since 6n+2 = 2(3n+1), 6n+3 = 3(2n+1), 6n+4 = 2(3n+2) are all composite for n ≥ 1,
   any prime q < 6n+5 with q ≥ 5 satisfies q ≤ 6n+1 < 6n+2.
5. This contradicts the survival hypothesis.
-/

/-
PROBLEM
Elements of Bk n k are positive for n ≥ 1.

PROVIDED SOLUTION
Case split on k (fin_cases k), then unfold Bk to get the definition of B1,...,B6 as Finset.Icc intervals. For each case, extract bounds from Finset.mem_Icc and show x > 0 using nlinarith with n ≥ 1. For example, for B1: x ≥ 6n²-2n+1 and n ≥ 1, so x ≥ 5 > 0.
-/
theorem Bk_pos (n : ℕ) (hn : n ≥ 1) (k : Fin 6) (x : ℤ) (hx : x ∈ Bk n k) :
    x > 0 := by
      fin_cases k <;> unfold Bk at hx;
      all_goals unfold B1 B2 B3 B4 B5 B6 at hx; norm_num at hx; nlinarith;

/-
PROBLEM
6x+1 is positive for x ∈ Bk n k with n ≥ 1.

PROVIDED SOLUTION
From Bk_pos, x > 0, so 6*x+1 ≥ 7 > 0. Use linarith with Bk_pos.
-/
theorem six_x_plus_one_pos (n : ℕ) (hn : n ≥ 1) (k : Fin 6) (x : ℤ) (hx : x ∈ Bk n k) :
    6 * x + 1 > 0 := by
      linarith [ Bk_pos n hn k x hx ]

/-
PROBLEM
6x-1 is positive for x ∈ Bk n k with n ≥ 1.

PROVIDED SOLUTION
From Bk_pos, x > 0, so 6*x-1 ≥ 5 > 0. Use linarith with Bk_pos.
-/
theorem six_x_minus_one_pos (n : ℕ) (hn : n ≥ 1) (k : Fin 6) (x : ℤ) (hx : x ∈ Bk n k) :
    6 * x - 1 > 0 := by
      have := Bk_pos n hn k x hx; linarith;

/-
PROBLEM
6x+1 is not divisible by 2, since 6x+1 is odd.

PROVIDED SOLUTION
6*x+1 = 2*(3*x) + 1, which is odd. If 2 ∣ 6*x+1, then 2 ∣ 1 (since 2 ∣ 6*x), contradiction. Use omega or decide after reducing modular arithmetic.
-/
theorem six_x_plus_one_odd (x : ℤ) : ¬ (2 : ℤ) ∣ (6 * x + 1) := by
  grind +ring

/-
PROBLEM
6x+1 is not divisible by 3, since 6x+1 ≡ 1 mod 3.

PROVIDED SOLUTION
6*x+1 = 3*(2*x) + 1, so 6*x+1 ≡ 1 mod 3. If 3 ∣ 6*x+1, then 3 ∣ 1, contradiction. Use omega or decide.
-/
theorem six_x_plus_one_not_div_three (x : ℤ) : ¬ (3 : ℤ) ∣ (6 * x + 1) := by
  grind

/-
PROBLEM
6x-1 is not divisible by 2, since 6x-1 is odd.

PROVIDED SOLUTION
6*x-1 = 2*(3*x) - 1 = 2*(3*x-1) + 1, which is odd. If 2 ∣ 6*x-1, then since 2 ∣ 6*x, we get 2 ∣ 1, contradiction.
-/
theorem six_x_minus_one_odd (x : ℤ) : ¬ (2 : ℤ) ∣ (6 * x - 1) := by
  lia

/-
PROBLEM
6x-1 is not divisible by 3, since 6x-1 ≡ 2 mod 3.

PROVIDED SOLUTION
6*x-1 = 3*(2*x) - 1 ≡ -1 ≡ 2 mod 3. If 3 ∣ 6*x-1, then 3 ∣ 1 since 3 ∣ 6*x, contradiction.
-/
theorem six_x_minus_one_not_div_three (x : ℤ) : ¬ (3 : ℤ) ∣ (6 * x - 1) := by
  grind +ring

/-
PROBLEM
For n ≥ 1, the numbers 6n+2, 6n+3, 6n+4 are all composite (not prime).

PROVIDED SOLUTION
6*n+2 = 2*(3*n+1). For n ≥ 1, 3*n+1 ≥ 4, so 6*n+2 has factor 2 and is ≥ 8, so it's not prime. Use Nat.Prime definition: it would need to not have proper divisors, but 2 is a proper divisor.
-/
theorem not_prime_6n_plus_2 (n : ℕ) (hn : n ≥ 1) : ¬ Nat.Prime (6 * n + 2) := by
  rw [ show 6 * n + 2 = 2 * ( 3 * n + 1 ) by ring, Nat.prime_mul_iff ] ; aesop

/-
PROVIDED SOLUTION
6*n+3 = 3*(2*n+1). For n ≥ 1, 2*n+1 ≥ 3, so 6*n+3 is divisible by 3 and ≥ 9, hence not prime.
-/
theorem not_prime_6n_plus_3 (n : ℕ) (hn : n ≥ 1) : ¬ Nat.Prime (6 * n + 3) := by
  rw [ show 6 * n + 3 = 3 * ( 2 * n + 1 ) by ring, Nat.prime_mul_iff ] ; aesop

/-
PROVIDED SOLUTION
6*n+4 = 2*(3*n+2). For n ≥ 1, 3*n+2 ≥ 5, so 6*n+4 is divisible by 2 and ≥ 10, hence not prime.
-/
theorem not_prime_6n_plus_4 (n : ℕ) (hn : n ≥ 1) : ¬ Nat.Prime (6 * n + 4) := by
  rw [ show 6 * n + 4 = 2 * ( 3 * n + 2 ) by ring, Nat.prime_mul_iff ] ; aesop

/-
PROBLEM
If x ∈ Bk n k and 6x+1 survives sieving by all primes p with 5 ≤ p < 6n+2,
    then 6x+1 is prime.

PROVIDED SOLUTION
By contradiction. Assume (6*x+1).natAbs is not prime.

First show (6*x+1).natAbs ≠ 1: since x ∈ Bk n k and n ≥ 1, by Bk_pos x > 0, so 6*x+1 ≥ 7, so (6*x+1).natAbs ≥ 7 ≠ 1.

Since (6*x+1).natAbs ≠ 1 and not prime, by Nat.minFac_prime it has a prime minimal factor mf = (6*x+1).natAbs.minFac, and by Nat.minFac_sq_le_self, mf² ≤ (6*x+1).natAbs.

From legendre_targeting: 6*x+1 < (6*n + k.val)². Since 6*x+1 > 0, (6*x+1).natAbs = (6*x+1).toNat, and mf² ≤ (6*x+1).natAbs < (6*n+k.val)² (after conversion), so mf < 6*n+k.val ≤ 6*n+5.

Now mf divides (6*x+1).natAbs, so (mf : ℤ) ∣ (6*x+1) (using Int.natAbs_dvd_natAbs). Since mf is prime and mf ≥ 2, and 2 ∤ (6*x+1) (by six_x_plus_one_odd) and 3 ∤ (6*x+1) (by six_x_plus_one_not_div_three), we get mf ≥ 5.

Since mf is prime with mf < 6*n+5 and mf ≥ 5: if mf < 6*n+2, apply h_survive to get contradiction. Otherwise mf ∈ {6*n+2, 6*n+3, 6*n+4}. By not_prime_6n_plus_2/3/4, none of these are prime, contradicting mf being prime. So mf < 6*n+2 and h_survive gives ¬(mf : ℤ) ∣ (6*x+1), contradiction.
-/
theorem sieve_survivor_prime_plus (n : ℕ) (hn : n ≥ 1) (k : Fin 6) (x : ℤ)
    (hx : x ∈ Bk n k)
    (h_survive : ∀ p : ℕ, p.Prime → 5 ≤ p → p < 6 * n + 2 → ¬((p : ℤ) ∣ (6 * x + 1))) :
    Nat.Prime (6 * x + 1).natAbs := by
      contrapose! h_survive;
      -- Let $p$ be the minimal prime factor of $6x + 1$.
      obtain ⟨p, hp_prime, hp_div⟩ : ∃ p, Nat.Prime p ∧ p ∣ (6 * x + 1).natAbs ∧ ∀ q, Nat.Prime q → q ∣ (6 * x + 1).natAbs → p ≤ q := by
        have h_min_fac : ∃ p, Nat.Prime p ∧ p ∣ (6 * x + 1).natAbs := by
          refine Nat.exists_prime_and_dvd ?_;
          cases abs_cases ( 6 * x + 1 ) <;> linarith [ Bk_pos n hn k x hx ];
        exact ⟨ Nat.find h_min_fac, Nat.find_spec h_min_fac |>.1, Nat.find_spec h_min_fac |>.2, fun q hq hq' => Nat.find_min' h_min_fac ⟨ hq, hq' ⟩ ⟩;
      refine' ⟨ p, hp_prime, _, _, _ ⟩;
      · contrapose! h_survive; interval_cases p <;> simp_all +decide ;
        · omega;
        · omega;
      · have hp_lt : p^2 ≤ (6 * x + 1).natAbs := by
          obtain ⟨ q, hq ⟩ := hp_div.left;
          rcases q with ( _ | _ | q ) <;> simp_all +decide [ sq ];
          · omega;
          · exact Nat.mul_le_mul_left _ ( hp_div _ ( Nat.minFac_prime ( by aesop ) ) ( Nat.minFac_dvd _ ) |> le_trans <| Nat.minFac_le_of_dvd ( by linarith ) <| by aesop );
        have hp_lt : (6 * x + 1).natAbs < (6 * n + 5) ^ 2 := by
          have := legendre_targeting n hn k x hx;
          rw [ ← @Nat.cast_lt ℤ ] ; norm_num ; cases abs_cases ( 6 * x + 1 ) <;> nlinarith only [ this, ‹_›, k.2 ];
        by_cases hp_ge : p ≥ 6 * n + 2;
        · have hp_cases : p = 6 * n + 2 ∨ p = 6 * n + 3 ∨ p = 6 * n + 4 := by
            have hp_cases : p < 6 * n + 5 := by
              nlinarith only [ hp_lt, ‹p ^ 2 ≤ ( 6 * x + 1 |> Int.natAbs ) › ];
            omega;
          rcases hp_cases with ( rfl | rfl | rfl ) <;> simp_all +decide [ Nat.prime_mul_iff ];
          · exact absurd hp_prime ( by rw [ show 6 * n + 2 = 2 * ( 3 * n + 1 ) by ring ] ; exact Nat.not_prime_mul ( by norm_num ) ( by linarith ) );
          · exact absurd hp_prime ( by rw [ show 6 * n + 3 = 3 * ( 2 * n + 1 ) by ring ] ; exact Nat.not_prime_mul ( by norm_num ) ( by linarith ) );
          · exact absurd hp_prime ( by rw [ show 6 * n + 4 = 2 * ( 3 * n + 2 ) by ring ] ; exact Nat.not_prime_mul ( by norm_num ) ( by linarith ) );
        · exact lt_of_not_ge hp_ge;
      · simpa [ ← Int.natCast_dvd_natCast ] using hp_div.1

/-
PROBLEM
If x ∈ Bk n k and 6x-1 survives sieving by all primes p with 5 ≤ p < 6n+2,
    then 6x-1 is prime.

PROVIDED SOLUTION
By contradiction. Assume (6*x-1).natAbs is not prime. Same structure as sieve_survivor_prime_plus but for 6*x-1 instead of 6*x+1. Use six_x_minus_one_odd, six_x_minus_one_not_div_three, Bk_pos, legendre_targeting, and not_prime_6n_plus_2/3/4.

The key differences: 6*x-1 > 0 from six_x_minus_one_pos. And 6*x-1 < 6*x+1 < (6*n+k)², so (6*x-1).natAbs < (6*n+k)² < (6*n+5)². The rest follows identically.
-/
theorem sieve_survivor_prime_minus (n : ℕ) (hn : n ≥ 1) (k : Fin 6) (x : ℤ)
    (hx : x ∈ Bk n k)
    (h_survive : ∀ p : ℕ, p.Prime → 5 ≤ p → p < 6 * n + 2 → ¬((p : ℤ) ∣ (6 * x - 1))) :
    Nat.Prime (6 * x - 1).natAbs := by
      apply_mod_cast prime_of_no_prime_factors_lt _ _ _;
      exact 6 * n + 5;
      · cases abs_cases ( 6 * x - 1 ) <;> linarith [ Bk_pos n hn k x hx ];
      · have h_bound : 6 * x - 1 < (6 * n + 5) ^ 2 := by
          have h_legendre : 6 * x + 1 < (6 * n + k.val) ^ 2 := by
            exact legendre_targeting n hn k x hx |>.2;
          fin_cases k <;> norm_num at * <;> linarith! [ sq_nonneg ( n : ℤ ) ] ;
        linarith [ abs_of_nonneg ( show 0 ≤ 6 * x - 1 by linarith [ Bk_pos n hn k x hx ] ) ];
      · intro p hp hp_lt hp_div
        by_cases hp_ge_5 : 5 ≤ p;
        · contrapose! h_survive;
          refine' ⟨ p, hp, hp_ge_5, _, _ ⟩;
          · by_cases hp_eq_6n3 : p = 6 * n + 3 ∨ p = 6 * n + 4 ∨ p = 6 * n + 5;
            · grind +suggestions;
            · cases Nat.Prime.eq_two_or_odd hp <;> omega;
          · simpa [ ← Int.natCast_dvd_natCast ] using hp_div;
        · interval_cases p <;> norm_num at * <;> omega

/-- The threshold N₀ beyond which the density estimate holds.
    (In principle this is a computable constant from the analytic bounds.) -/
def N₀ : ℕ := 100

/-- **Analytic Density Substitution** (Open Problem)

    The density of survivors from small-prime sieving exceeds the effective
    coverage capacity of P_large for n ≥ N₀. This is the key analytic estimate
    integrating the Turán variance bounds (with the halved diagonal from Task 7)
    and the optimal weights from OptimalWeights.

    The proof would rely on:
    1. Mertens' theorem: ∏_{p ≤ 2n} (1 - 1/p) ~ 2e^{⁻γ}/log(2n)
    2. The variance halving (Task 7) which doubles the effective survivor density.
    3. The prime number theorem estimate: |P_large| ~ π(6n) - π(2n) ~ 4n/log(6n).
    4. For large enough n, the survivor count 2·(2n+1)·∏(1-1/p) exceeds |P_large| + |wasted|.

    **Status**: This inequality is equivalent to Legendre's Conjecture (that there is
    always a prime between n² and (n+1)²), which remains an open problem in number theory.
    The best unconditional prime gap result (Baker-Harman-Pintz, 2001) guarantees
    primes in [x, x + x^{0.525}], but Legendre requires gaps of size O(x^{0.5}),
    which is beyond current unconditional mathematical knowledge.

    Everything else in the proof pipeline is fully verified. We pass this analytic 
    limit as the explicit hypothesis `h_density` to conditionally close the sequence.

    The Legendre conjecture holds conditionally for all n ≥ N₀: there exists a prime between
    consecutive squares in each Krafft window. Specifically, for some k : Fin 6,
    there exists x ∈ Bk n k such that either 6x+1 or 6x-1 is prime, and by the
    Legendre targeting property this prime lies strictly between (6n+k-1)² and (6n+k)². -/
theorem legendre_conjecture_holds_conditional (n : ℕ) (hn : n ≥ N₀)
    (h_density : ∃ k : Fin 6, (U_plus n k).card + (U_minus n k).card >
      (P_large n).card + (wasted_primes n k).card) :
    ∃ k : Fin 6, ∃ x ∈ Bk n k,
      (Nat.Prime (6 * x + 1).natAbs ∧ (6 * (n : ℤ) + k.val - 1) ^ 2 < 6 * x + 1
        ∧ 6 * x + 1 < (6 * (n : ℤ) + k.val) ^ 2) ∨
      (Nat.Prime (6 * x - 1).natAbs ∧ (6 * (n : ℤ) + k.val - 1) ^ 2 < 6 * x - 1
        ∧ 6 * x - 1 < (6 * (n : ℤ) + k.val) ^ 2) := by
  -- Step 1: Get the density estimate for some k from the conditional hypothesis
  obtain ⟨k, hk⟩ := h_density
  use k
  -- Step 2: Apply survivor_exists to get a sieve survivor
  have hn1 : n ≥ 1 := le_trans (by unfold N₀; omega) hn
  have h_surv := survivor_exists n hn1 k hk
  -- Step 3: The survivor is prime by the bridge lemma
  rcases h_surv with ⟨x, hx_mem, hx_survive⟩ | ⟨x, hx_mem, hx_survive⟩
  · -- Case: x survives S⁺ sieving
    refine ⟨x, hx_mem, Or.inl ⟨sieve_survivor_prime_plus n hn1 k x hx_mem hx_survive, ?_, ?_⟩⟩
    · have := (legendre_targeting n hn1 k x hx_mem).1; linarith
    · exact (legendre_targeting n hn1 k x hx_mem).2
  · -- Case: x survives S⁻ sieving
    refine ⟨x, hx_mem, Or.inr ⟨sieve_survivor_prime_minus n hn1 k x hx_mem hx_survive, ?_, ?_⟩⟩
    · exact (legendre_targeting n hn1 k x hx_mem).1
    · have := (legendre_targeting n hn1 k x hx_mem).2; linarith

end