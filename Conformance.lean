import KrafftSieve

open KrafftSieve

/-- Definition of the set of primes primeWindow.
Let $\mathcal{P}_n$ denote the set of primes $p$ such that $5 \le p < 6n+2$. -/
example (n : ℕ) : Finset ℕ := primeWindow n

/-- The main term of the sieve: 2H(n) -/
noncomputable example (n : ℕ) : ℝ := mainTerm n

/-- The total resonance capacity: Σ (2/p)·cos(π/p) -/
noncomputable example (n : ℕ) : ℝ := resonanceCapacity n

/--
The Harmonic Deficit (Parity Barrier Collision)
The resonance capacity of any purely one-dimensional 3rd harmonic weight system is strictly
overpowered by the sieve aggregate main density. This formalizes the collision with the
Sieve Parity limit.
-/
example (n : ℕ) (hn : primeWindow n ≠ ∅) :
    resonanceCapacity n < mainTerm n :=
  resonance_lt_mainTerm n hn

/-- Define evalInterval
Define the target interval of indices:
evalInterval = {x in N | 6n^2 - 2n <= x <= 6n^2 + 10n + 3}. -/
example (n : ℕ) : Finset ℕ := evalInterval n

/--
Definition of the Krafft Sufficiency condition
Existence of a weight function $W$ such that $sum2(n, W) < sum1(n, W)$.
-/
example (n : ℕ) : Prop := KrafftSufficiency n

/-
The Krafft Sieve Guarantee:
Admit that there exists a valid non-negative weight function $W(x)$ supported on
$\mathcal{A}_n$ such that the magnitude of the negative third-harmonic resonance strictly
overpowers the main term, yielding:
$$ sum2(n, W) < sum1(n, W) $$
Conclude that by the Weighted Existence Principle and the Additive Sieve Equivalence, a Twin Prime
index is unconditionally guaranteed in $\mathcal{A}_n$.
-/
example (n : ℕ) (hn : n ≥ 1) (h_admit : KrafftSufficiency n) :
    ∃ x ∈ evalInterval n, Nat.Prime (6 * x - 1) ∧ Nat.Prime (6 * x + 1) :=
  krafft_sieve_guarantee n hn h_admit

/--
Define $\mu_{min}(n)$ as the infimum of the attainable ratios.
-/
noncomputable example (n : ℕ) : ℝ := muMin n

/--
Theorem: The Krafft Sieve Guarantee holds if $\mu_{min}(n) < 1$.
-/
example (n : ℕ) (h : muMin n < 1) :
    ∃ x ∈ evalInterval n, Nat.Prime (6 * x - 1) ∧ Nat.Prime (6 * x + 1) :=
  krafft_sieve_guarantee_with_mu_min n h

/--
Theorem: If there are infinitely many intervals where the optimal multidimensional
weight achieves a ratio strictly less than 1, then there are infinitely many twin primes.
-/
example :
    {n : ℕ | muMin n < 1}.Infinite
    → {p : ℕ | Prime p ∧ Prime (p + 2)}.Infinite :=
  mu_min_lt_one_implies_tpc
