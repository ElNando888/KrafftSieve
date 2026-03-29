/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela

Task 3: Turán Statistical Bounds (Reusing Variance.lean)
Sets up theorems applying optimal weights over P_small, defines the residual survivor
sets U⁺ and U⁻, and hooks up expected combinatorial density.
-/

import Legendre.SieveSplitting
import KrafftSieve.Variance
import KrafftSieve.OptimalWeights

open scoped BigOperators

set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option linter.style.refine false
set_option linter.style.nativeDecide false
set_option linter.flexible false
set_option linter.style.induction false
set_option linter.style.emptyLine false

open Classical in
noncomputable section

/-! ## Residual survivor sets -/

/-- A Krafft sub-interval as a Finset ℤ (re-export for convenience). -/
abbrev KrafftInterval (n : ℕ) (k : Fin 6) : Finset ℤ := Bk n k

/-- The set U⁺ of "holes" surviving S⁺ sieving by P_small in interval B_n^(k):
    those x ∈ B_n^(k) such that no small prime p divides 6x + 1. -/
noncomputable def U_plus (n : ℕ) (k : Fin 6) : Finset ℤ :=
  (Bk n k).filter (fun x =>
    ∀ p ∈ P_small n, ¬((p : ℤ) ∣ (6 * x + 1)))

/-- The set U⁻ of "holes" surviving S⁻ sieving by P_small in interval B_n^(k):
    those x ∈ B_n^(k) such that no small prime p divides 6x - 1. -/
noncomputable def U_minus (n : ℕ) (k : Fin 6) : Finset ℤ :=
  (Bk n k).filter (fun x =>
    ∀ p ∈ P_small n, ¬((p : ℤ) ∣ (6 * x - 1)))

/-- U⁺ is a subset of the Krafft interval. -/
theorem U_plus_subset (n : ℕ) (k : Fin 6) : U_plus n k ⊆ Bk n k :=
  Finset.filter_subset _ _

/-- U⁻ is a subset of the Krafft interval. -/
theorem U_minus_subset (n : ℕ) (k : Fin 6) : U_minus n k ⊆ Bk n k :=
  Finset.filter_subset _ _

/-! ## Expected combinatorial density -/

/-- The expected density of survivors from small-prime sieving is approximately
    L · ∏_{p ≤ 2n} (1 - 1/p). We define the product factor here. -/
noncomputable def mertens_product (n : ℕ) : ℝ :=
  ∏ p ∈ P_small n, (1 - 1 / (p : ℝ))

/-- The expected number of S⁺ survivors (heuristic upper bound). -/
noncomputable def expected_U_plus_card (n : ℕ) : ℝ :=
  (2 * n + 1 : ℝ) * mertens_product n

/-- The expected number of S⁻ survivors (heuristic upper bound). -/
noncomputable def expected_U_minus_card (n : ℕ) : ℝ :=
  (2 * n + 1 : ℝ) * mertens_product n

/-! ## Turán-type large sieve inequality setup -/

/-
PROBLEM
For each small prime p, it is bounded by 2n.

PROVIDED SOLUTION
From the definition of P_small: it filters range(2n+1), so p < 2n+1, hence p ≤ 2n.
-/
theorem small_prime_coverage (n : ℕ) (hn : n ≥ 1) (p : ℕ) (hp : p ∈ P_small n) :
    p ≤ 2 * n := by
      exact Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hp |>.1 )

/-
PROBLEM
The number of small sieving primes is bounded by π(2n) (the prime counting function).

PROVIDED SOLUTION
P_small n is the set of primes p with 5 ≤ p < 2n+1, which is a subset of primes less than or equal to 2n. The cardinality of all primes ≤ 2n is Nat.primeCounting(2n). Since P_small ⊆ {p prime | p ≤ 2n}, its card is ≤ primeCounting(2n). More precisely, P_small n ⊆ (Finset.range (2n+1)).filter Nat.Prime, and (Finset.range (2n+1)).filter Nat.Prime has card = Nat.primeCounting(2n). Then P_small is a subset of this (it has the extra constraint 5 ≤ p), so its card is ≤.
-/
theorem P_small_card_bound (n : ℕ) : (P_small n).card ≤ Nat.primeCounting (2 * n) := by
  -- Since P_small n is a subset of the set of primes less than or equal to 2n, we can conclude that its cardinality is less than or equal to the cardinality of the set of primes less than or equal to 2n.
  have h_subset : P_small n ⊆ Finset.filter Nat.Prime (Finset.range (2 * n + 1)) := by
    exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hx |>.1, Finset.mem_filter.mp hx |>.2.2 ⟩;
  nontriviality;
  rw [ Nat.primeCounting ];
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
  exact Finset.card_le_card h_subset

/-! ## Task 6: Sieve Indicator Definitions and Variance Instantiation -/

/-- S⁺ indicator for prime p at point x: 1 if p ∣ 6x+1, 0 otherwise.
    This is the indicator function I_p⁺(x) from the Turán sieve. -/
def I_plus_ind (p : ℕ) (x : ℤ) : ℕ :=
  if (p : ℤ) ∣ (6 * x + 1) then 1 else 0

/-- S⁻ indicator for prime p at point x: 1 if p ∣ 6x−1, 0 otherwise.
    This is the indicator function I_p⁻(x) from the Turán sieve. -/
def I_minus_ind (p : ℕ) (x : ℤ) : ℕ :=
  if (p : ℤ) ∣ (6 * x - 1) then 1 else 0

/-- The aggregate sieve indicator I_p(x) = I_p⁺(x) + I_p⁻(x), counting the total
    number of sieve hits (0, 1, or 2) from prime p on point x. -/
def I_total_ind (p : ℕ) (x : ℤ) : ℕ :=
  I_plus_ind p x + I_minus_ind p x

/-- The aggregate hit count over all small primes P_small for a given point x. -/
def aggregate_hits_small (n : ℕ) (x : ℤ) : ℕ :=
  ∑ p ∈ P_small n, I_total_ind p x

/-! ## Task 7: The Diagonal Krafft Separation -/

/-
PROBLEM
Key separation lemma: no prime p ≥ 5 can simultaneously divide both 6x+1 and 6x−1.
    If p ∣ 6x+1 and p ∣ 6x−1, then p ∣ (6x+1)−(6x−1) = 2. But p ≥ 5 > 2, contradiction.
    This means I_p⁺(x) · I_p⁻(x) = 0 for all x.

PROVIDED SOLUTION
Unfold I_plus_ind and I_minus_ind. If (p : ℤ) ∤ (6*x+1) or (p : ℤ) ∤ (6*x-1), then one factor is 0 so the product is 0. If both divide, then p ∣ (6*x+1) - (6*x-1) = 2, but p ≥ 5 so p ∤ 2, contradiction. Use Int.Prime.not_dvd or direct argument that p ≥ 5 implies ¬(p : ℤ) ∣ 2.
-/
theorem I_plus_mul_I_minus_eq_zero (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (x : ℤ) :
    I_plus_ind p x * I_minus_ind p x = 0 := by
      unfold I_plus_ind I_minus_ind;
      split_ifs <;> simp_all +decide [ sub_eq_add_neg ];
      exact absurd ( Int.dvd_sub ‹ ( p : ℤ ) ∣ 6 * x + 1 › ‹ ( p : ℤ ) ∣ 6 * x + -1 › ) ( by norm_num; exact mod_cast Nat.not_dvd_of_pos_of_lt ( by norm_num ) ( by linarith ) )

/-
PROBLEM
I_plus_ind takes values in {0, 1}.

PROVIDED SOLUTION
Unfold I_plus_ind. It's an if-then-else returning 1 or 0, both ≤ 1.
-/
theorem I_plus_ind_le_one (p : ℕ) (x : ℤ) : I_plus_ind p x ≤ 1 := by
  unfold I_plus_ind; aesop;

/-
PROBLEM
I_minus_ind takes values in {0, 1}.

PROVIDED SOLUTION
Unfold I_minus_ind. It's an if-then-else returning 1 or 0, both ≤ 1.
-/
theorem I_minus_ind_le_one (p : ℕ) (x : ℤ) : I_minus_ind p x ≤ 1 := by
  unfold I_minus_ind; aesop;

/-
PROBLEM
I_plus_ind squared equals itself (idempotent, since it's 0 or 1).

PROVIDED SOLUTION
Unfold I_plus_ind. Split on the if condition. If true, result is 1^2 = 1. If false, result is 0^2 = 0.
-/
theorem I_plus_ind_sq (p : ℕ) (x : ℤ) : I_plus_ind p x ^ 2 = I_plus_ind p x := by
  unfold I_plus_ind; aesop;

/-
PROBLEM
I_minus_ind squared equals itself (idempotent, since it's 0 or 1).

PROVIDED SOLUTION
Unfold I_minus_ind. Split on the if condition. If true, result is 1^2 = 1. If false, result is 0^2 = 0.
-/
theorem I_minus_ind_sq (p : ℕ) (x : ℤ) : I_minus_ind p x ^ 2 = I_minus_ind p x := by
  unfold I_minus_ind; aesop;

/-
PROBLEM
The variance halving identity: because I_p⁺ and I_p⁻ are disjoint (their product is 0),
    the square of the aggregate indicator simplifies:
    (I_p⁺ + I_p⁻)² = (I_p⁺)² + 2·I_p⁺·I_p⁻ + (I_p⁻)² = I_p⁺ + 0 + I_p⁻ = I_p⁺ + I_p⁻.
    This strictly halves the diagonal penalty in the Turán variance matrix.

PROVIDED SOLUTION
Unfold I_total_ind. We need (I_plus_ind p x + I_minus_ind p x)^2 = I_plus_ind p x + I_minus_ind p x. Expand the square: a^2 + 2ab + b^2 = a + b. Since a^2 = a (I_plus_ind_sq), b^2 = b (I_minus_ind_sq), and a*b = 0 (I_plus_mul_I_minus_eq_zero), this simplifies to a + 0 + b = a + b.
-/
theorem I_total_sq_eq_self (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (x : ℤ) :
    I_total_ind p x ^ 2 = I_total_ind p x := by
      unfold I_total_ind;
      unfold I_plus_ind I_minus_ind ; split_ifs <;> norm_num;
      have := Int.dvd_sub ‹ ( p : ℤ ) ∣ 6 * x + 1 › ‹ ( p : ℤ ) ∣ 6 * x - 1 ›; norm_num at this; norm_cast at this; have := Nat.le_of_dvd ( by linarith ) this; interval_cases p ;

end
