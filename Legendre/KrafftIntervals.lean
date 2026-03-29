/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela

Task 1: Explicit Krafft Sequences and Sieves
Formalizes the integer range A_n and its exact disjoint partitions B_n^(k),
proves the Legendre targeting property and cardinality bounds,
and defines the sieve indicator hits S^+ and S^-.
-/

-- import Mathlib
import KrafftSieve.Defs

open scoped BigOperators

set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option linter.style.refine false
set_option linter.style.nativeDecide false
set_option linter.flexible false
set_option linter.style.induction false
set_option linter.style.emptyLine false

noncomputable section

/-! ## Krafft Interval Definitions -/

/-- Krafft sub-interval B_n^(1) = {6n² - 2n + 1, ..., 6n² - 1}. -/
def B1 (n : ℕ) : Finset ℤ :=
  Finset.Icc (6 * (n : ℤ) ^ 2 - 2 * n + 1) (6 * n ^ 2 - 1)

/-- Krafft sub-interval B_n^(2) = {6n² + 1, ..., 6n² + 2n - 1}. -/
def B2 (n : ℕ) : Finset ℤ :=
  Finset.Icc (6 * (n : ℤ) ^ 2 + 1) (6 * n ^ 2 + 2 * n - 1)

/-- Krafft sub-interval B_n^(3) = {6n² + 2n + 1, ..., 6n² + 4n}. -/
def B3 (n : ℕ) : Finset ℤ :=
  Finset.Icc (6 * (n : ℤ) ^ 2 + 2 * n + 1) (6 * n ^ 2 + 4 * n)

/-- Krafft sub-interval B_n^(4) = {6n² + 4n + 1, ..., 6n² + 6n + 1}. -/
def B4 (n : ℕ) : Finset ℤ :=
  Finset.Icc (6 * (n : ℤ) ^ 2 + 4 * n + 1) (6 * n ^ 2 + 6 * n + 1)

/-- Krafft sub-interval B_n^(5) = {6n² + 6n + 2, ..., 6n² + 8n + 2}. -/
def B5 (n : ℕ) : Finset ℤ :=
  Finset.Icc (6 * (n : ℤ) ^ 2 + 6 * n + 2) (6 * n ^ 2 + 8 * n + 2)

/-- Krafft sub-interval B_n^(6) = {6n² + 8n + 3, ..., 6n² + 10n + 3}. -/
def B6 (n : ℕ) : Finset ℤ :=
  Finset.Icc (6 * (n : ℤ) ^ 2 + 8 * n + 3) (6 * n ^ 2 + 10 * n + 3)

/-- Accessor for the k-th Krafft sub-interval, k ∈ {0,...,5} (0-indexed). -/
def Bk (n : ℕ) : Fin 6 → Finset ℤ
  | ⟨0, _⟩ => B1 n
  | ⟨1, _⟩ => B2 n
  | ⟨2, _⟩ => B3 n
  | ⟨3, _⟩ => B4 n
  | ⟨4, _⟩ => B5 n
  | ⟨5, _⟩ => B6 n

/-! ## Cardinality bounds -/

/-- Each Krafft sub-interval has cardinality at most 2n + 1. -/
theorem Bk_card_le (n : ℕ) (k : Fin 6) : (Bk n k).card ≤ 2 * n + 1 := by
  revert k;
  intros k
  simp [Bk];
  fin_cases k <;> simp +decide [ B1, B2, B3, B4, B5, B6 ] <;> omega;

/-! ## Legendre targeting property -/

/-
PROBLEM
For x ∈ B_n^(k) (0-indexed k), both 6x - 1 and 6x + 1 lie strictly between
    consecutive squares (6n + k - 1)² and (6n + k)².
    This matches the tex convention: B^(k+1) targets between (6n+(k+1)-2)² and (6n+(k+1)-1)²
    = (6n+k-1)² and (6n+k)².

PROVIDED SOLUTION
Case split on k (fin_cases k). For each k=j (0-indexed), unfold Bk to get the interval bounds on x from Finset.Icc membership. Then the inequalities become purely algebraic: use nlinarith with the bounds on x and n ≥ 1. For example, k=0 (B1): x ∈ [6n²-2n+1, 6n²-1]. Need (6n-1)² < 6x-1, i.e. 36n²-12n+1 < 6x-1, i.e. x > 6n²-2n, which holds since x ≥ 6n²-2n+1. And 6x+1 < (6n)² = 36n², i.e. x < 6n²-1/6, which holds since x ≤ 6n²-1.
-/
theorem legendre_targeting (n : ℕ) (hn : n ≥ 1) (k : Fin 6) (x : ℤ)
    (hx : x ∈ Bk n k) :
    (6 * (n : ℤ) + k.val - 1) ^ 2 < 6 * x - 1 ∧
    6 * x + 1 < (6 * (n : ℤ) + k.val) ^ 2 := by
      fin_cases k <;> simp +decide [ Bk ] at hx ⊢;
      all_goals erw [ Finset.mem_Icc ] at hx; constructor <;> nlinarith;

/-! ## Sieve hit indicators -/

/-- For a sieving prime p = 6m + α (α ∈ {1, -1}), the S⁺ residue class
    (representing p ∣ 6x + 1) hits x ≡ α·m (mod p). -/
def sieve_hit_plus (p : ℕ) (m : ℤ) (alpha : ℤ) : ZMod p :=
  (alpha * m : ℤ)

/-- For a sieving prime p = 6m + α (α ∈ {1, -1}), the S⁻ residue class
    (representing p ∣ 6x - 1) hits x ≡ -α·m (mod p). -/
def sieve_hit_minus (p : ℕ) (m : ℤ) (alpha : ℤ) : ZMod p :=
  (-alpha * m : ℤ)

/-
PROBLEM
The S⁺ hit is correct: if p = 6m + α and x ≡ α·m (mod p), then p ∣ 6x + 1.

PROVIDED SOLUTION
We need to show p ∣ 6x + 1 given p = 6m + α and x ≡ αm (mod p). Rewrite divisibility as (6x+1 : ZMod p) = 0. From hx, (x : ZMod p) = (α*m : ZMod p). So (6*x+1 : ZMod p) = (6*α*m+1 : ZMod p). Since (p : ZMod p) = 0, we get (6m + α : ZMod p) = 0, hence 6m ≡ -α (mod p). Then 6*α*m = α*(6m) ≡ α*(-α) = -α² = -1 (mod p). So 6x+1 ≡ -1+1 = 0 (mod p). Use ← ZMod.intCast_zmod_eq_zero_iff_dvd to reduce to ZMod computation, then use ring-like reasoning or direct substitution.
-/
theorem sieve_hit_plus_correct (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (m : ℤ) (alpha : ℤ) (halpha : alpha = 1 ∨ alpha = -1)
    (hp_eq : (p : ℤ) = 6 * m + alpha) (x : ℤ) (hx : (x : ZMod p) = sieve_hit_plus p m alpha) :
    (p : ℤ) ∣ 6 * x + 1 := by
      -- Substitute $x$ from hypothesis hx into the expression $6x + 1$.
      have h_subst : (6 * x + 1 : ℤ) ≡ (6 * (alpha * m) + 1 : ℤ) [ZMOD p] := by
        have h_subst : (x : ℤ) ≡ (alpha * m : ℤ) [ZMOD p] := by
          exact (ZMod.intCast_eq_intCast_iff x (alpha * m) p).mp hx;
        gcongr;
      exact Int.dvd_of_emod_eq_zero ( h_subst.symm ▸ Int.emod_eq_zero_of_dvd ( by rcases halpha with ( rfl | rfl ) <;> [ exact ⟨ 1, by linarith ⟩ ; exact ⟨ -1, by linarith ⟩ ] ) )

/-- The S⁻ hit is correct: if p = 6m + α and x ≡ -α·m (mod p), then p ∣ 6x - 1. -/
theorem sieve_hit_minus_correct (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (m : ℤ) (alpha : ℤ) (halpha : alpha = 1 ∨ alpha = -1)
    (hp_eq : (p : ℤ) = 6 * m + alpha) (x : ℤ) (hx : (x : ZMod p) = sieve_hit_minus p m alpha) :
    (p : ℤ) ∣ 6 * x - 1 := by
      have h_sub : (6 * x - 1 : ℤ) ≡ (6 * (-alpha * m) - 1 : ℤ) [ZMOD p] := by
        unfold sieve_hit_minus at hx; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
        simp +decide [ ← hp_eq, ← ZMod.intCast_eq_intCast_iff, hx ];
      exact Int.dvd_of_emod_eq_zero ( h_sub.symm ▸ Int.modEq_zero_iff_dvd.2 ( by obtain rfl | rfl := halpha <;> [ exact ⟨ -1, by linarith ⟩ ; exact ⟨ 1, by linarith ⟩ ] ) )

end
