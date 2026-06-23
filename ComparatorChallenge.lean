/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting

/-
Note: the imports are copied directly from the project's original file. For some unknown reason,
using a simple `import Mathlib` induces an incorrect "Const does not match" error.
-/

namespace KrafftSieve

/-- Definition of the set of primes primeWindow.
Let $\mathcal{P}_n$ denote the set of primes $p$ such that $5 \le p < 6n+2$. -/
def primeWindow (n : ℕ) : Finset ℕ :=
  (Finset.range (6 * n + 2)).filter (fun p => 5 ≤ p ∧ p.Prime)

/-- Definition of the primorial q.
Define the primorial $q = \prod_{p \in \mathcal{P}_n} p$. -/
def q (n : ℕ) : ℕ := (primeWindow n).prod (fun p => p)

/-- Definition of w as the cardinality of primeWindow.
Let $w = |\mathcal{P}_n|$ be the number of distinct prime factors of $q$. -/
def w (n : ℕ) : ℕ := (primeWindow n).card

/-- Definition of the sorted list of primes and the accessor function p_i.
Index the primes in $\mathcal{P}_n$ as $p_1, p_2, \dots, p_w$. -/
def primesList (n : ℕ) : List ℕ := (primeWindow n).sort (· ≤ ·)

/-- Access the $i$-th prime $p_i$. Note that we use 0-based indexing for the implementation,
so $p_0$ corresponds to the user's $p_1$. -/
def p (n : ℕ) (i : Fin (w n)) : ℕ := (primesList n).get (i.cast (by
  unfold w primesList
  simp_all only [Finset.length_sort]))

/-- Define r^K
Define the Krafft tuple r^K such that for each 1 <= i <= w,
r^K_i = floor((p_i+1)/6). -/
def krafftResidue (n : ℕ) (i : Fin (w n)) : ℕ := (p n i + 1) / 6

/-- Define evalInterval
Define the target interval of indices:
evalInterval = {x in N | 6n^2 - 2n <= x <= 6n^2 + 10n + 3}. -/
def evalInterval (n : ℕ) : Finset ℕ :=
  Finset.Icc (6 * n ^ 2 - 2 * n) (6 * n ^ 2 + 10 * n + 3)

/-- Define the local hit function g_i(x)
Define the local hit function $g_i : \mathbb{Z}/q\mathbb{Z} \to \mathbb{R}$
for each prime index $i \in \{1, \dots, w\}$.
- $g_i(x) = 1$ if $x \equiv r^K_i \pmod{p_i}$ or $x \equiv -r^K_i \pmod{p_i}$.
- Otherwise, $g_i(x) = 0$. -/
noncomputable def g (n : ℕ) (i : Fin (w n)) (x : ZMod (q n)) : ℝ :=
  if (x.cast : ZMod (p n i)) = (krafftResidue n i : ZMod (p n i))
    ∨ (x.cast : ZMod (p n i)) = -(krafftResidue n i : ZMod (p n i))
  then 1 else 0

/-- Define the global additive hit counter c(x)
Define the global additive hit counter
$c : \mathbb{Z}/q\mathbb{Z} \to \mathbb{R}$ as the sum of all local hits:
$$ c(x) = \sum_{i=1}^w g_i(x) $$ -/
noncomputable def c (n : ℕ) (x : ZMod (q n)) : ℝ :=
  ∑ i : Fin (w n), g n i x

/--
Define the basis function for a subset of prime indices $S \subseteq \{1, \dots, w\}$.
The basis function is the product of the 3rd harmonic cosines for each prime in $S$.
$$ B_S(x) = \prod_{i \in S} \cos\left( \frac{6\pi x}{p_i} \right) $$
-/
noncomputable def basisCos (n : ℕ) (S : Finset (Fin (w n))) (x : ZMod (q n)) : ℝ :=
  ∏ i ∈ S, Real.cos (2 * Real.pi * 3 * (x.val : ℝ) / (p n i : ℝ))

/--
Define the matrix $M_1$ corresponding to the first moment $sum1$.
$M_1(S, T) = \sum_{x \in \mathcal{A}_n} B_S(x) B_T(x)$
-/
noncomputable def matrix1 (n : ℕ) (S T : Finset (Fin (w n))) : ℝ :=
  ∑ x ∈ evalInterval n, basisCos n S (x : ZMod (q n)) * basisCos n T (x : ZMod (q n))

/--
Define the matrix $M_2$ corresponding to the second moment $sum2$.
$M_2(S, T) = \sum_{x \in \mathcal{A}_n} c(x) B_S(x) B_T(x)$
-/
noncomputable def matrix2 (n : ℕ) (S T : Finset (Fin (w n))) : ℝ :=
  ∑ x ∈ evalInterval n, c n (x : ZMod (q n)) * basisCos n S (x : ZMod (q n)) *
    basisCos n T (x : ZMod (q n))

/--
Define the quadratic form $q1(\lambda) = \lambda^T M_1 \lambda$.
-/
noncomputable def q1 (n : ℕ) (lambda : Finset (Fin (w n)) → ℝ) : ℝ :=
  ∑ S ∈ Finset.univ.powerset, ∑ T ∈ Finset.univ.powerset, lambda S * matrix1 n S T * lambda T

/--
Define the quadratic form $q2(\lambda) = \lambda^T M_2 \lambda$.
-/
noncomputable def q2 (n : ℕ) (lambda : Finset (Fin (w n)) → ℝ) : ℝ :=
  ∑ S ∈ Finset.univ.powerset, ∑ T ∈ Finset.univ.powerset, lambda S * matrix2 n S T * lambda T

/--
Define the Rayleigh quotient $R(\lambda) = \frac{q2(\lambda)}{q1(\lambda)}$.
Defined to be $\infty$ if $q1(\lambda) = 0$ (though $q1$ is positive definite on
non-zero $\lambda$ if the basis is linearly independent on $evalInterval$).
-/
noncomputable def Ratio (n : ℕ) (lambda : Finset (Fin (w n)) → ℝ) : ℝ :=
  if q1 n lambda = 0 then 0 else (q2 n lambda) / (q1 n lambda)

/--
Define the set of attainable ratios.
-/
def attainableRatios (n : ℕ) : Set ℝ :=
  { r | ∃ lambda : Finset (Fin (w n)) → ℝ, q1 n lambda > 0 ∧ r = Ratio n lambda }

/--
Define $\mu_{min}(n)$ as the infimum of the attainable ratios.
-/
noncomputable def muMin (n : ℕ) : ℝ := sInf (attainableRatios n)

/--
Theorem: If there are infinitely many intervals where the optimal multidimensional
weight achieves a ratio strictly less than 1, then there are infinitely many twin primes.
-/
theorem mu_min_lt_one_implies_tpc :
    {n : ℕ | muMin n < 1}.Infinite
    → {p : ℕ | Prime p ∧ Prime (p + 2)}.Infinite := by
  sorry

end KrafftSieve
