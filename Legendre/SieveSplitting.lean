/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela

Task 2: Sieve Splitting Subsets
Defines the partition of sieving primes into P_small (statistical) and P_large (geometric)
relative to interval length L = 2n.
-/

import Mathlib
import Legendre.KrafftIntervals

open scoped BigOperators

set_option linter.style.setOption false
set_option linter.style.longLine false

noncomputable section

/-! ## Sieve splitting definitions -/

/-- The set of small sieving primes: p prime with 5 ≤ p ≤ 2n. -/
def P_small (n : ℕ) : Finset ℕ :=
  (Finset.range (2 * n + 1)).filter (fun p => 5 ≤ p ∧ p.Prime)

/-- The set of large sieving primes: p prime with 2n < p < 6n + 2. -/
def P_large (n : ℕ) : Finset ℕ :=
  ((Finset.range (6 * n + 2)).filter (fun p => 2 * n < p ∧ 5 ≤ p ∧ p.Prime))

/-
PROBLEM
P_small and P_large are disjoint.

PROVIDED SOLUTION
The disjointness is immediate: P_small has p ≤ 2n (range (2n+1) means p < 2n+1, i.e. p ≤ 2n), while P_large has p > 2n. These are disjoint by the strict inequality.
-/
theorem P_small_P_large_disjoint (n : ℕ) : Disjoint (P_small n) (P_large n) := by
  -- To prove disjointness, we show that the ranges of primes in P_small and P_large are disjoint.
  have h_range_disjoint : ∀ p, p ∈ P_small n → p ∉ P_large n := by
    unfold P_small P_large; aesop;
  exact Finset.disjoint_left.mpr h_range_disjoint

/-
PROBLEM
Every sieving prime (5 ≤ p < 6n+2, p prime) is in P_small ∪ P_large.

PROVIDED SOLUTION
If p ≤ 2n then p < 2n+1 so p ∈ range(2n+1), hence p ∈ P_small. If p > 2n then p ∈ P_large since p < 6n+2 and p is prime with p ≥ 5.
-/
theorem sieve_primes_partition (n : ℕ) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (hlt : p < 6 * n + 2) :
    p ∈ P_small n ∨ p ∈ P_large n := by
      cases lt_or_ge p ( 2 * n + 1 ) <;> unfold P_small P_large <;> aesop

/-
PROBLEM
For any p ∈ P_large, p > 2n (the interval length L).

PROVIDED SOLUTION
Directly from the definition of P_large: the filter condition includes 2*n < p.
-/
theorem P_large_gt_L (n : ℕ) (p : ℕ) (hp : p ∈ P_large n) : p > 2 * n := by
  unfold P_large at hp; aesop;

end
