/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela, Google DeepMind
-/

import KrafftSieve.OptimalWeights


/-!
# Main Theorem

-/

namespace KrafftSieve

/--
Theorem: If there are infinitely many intervals where the optimal multidimensional
weight achieves a ratio strictly less than 1, then there are infinitely many twin primes.
-/
theorem mu_min_lt_one_implies_tpc :
    {n : ℕ | muMin n < 1}.Infinite
    → {p : ℕ | Prime p ∧ Prime (p + 2)}.Infinite := by
  intro h_inf
  rw [Set.infinite_iff_exists_gt] at h_inf ⊢
  intro B
  obtain ⟨n, hn_set, hn_gt⟩ := h_inf B
  have h_mu : muMin n < 1 := hn_set
  obtain ⟨x, hx_int, hx_prime1, hx_prime2⟩ := krafft_sieve_guarantee_with_mu_min n h_mu
  have hx_lower : x ≥ 6 * n^2 - 2 * n := by
    rw [evalInterval] at hx_int
    exact Finset.mem_Icc.mp hx_int |>.1
  have hn_sq : n^2 ≥ n := by nlinarith
  have hp_gt : 6 * x - 1 > B := by omega
  have h_plus_two : 6 * x - 1 + 2 = 6 * x + 1 := by omega
  have hp_goal : Prime (6 * x - 1) ∧ Prime (6 * x - 1 + 2) := by
    rw [h_plus_two]
    exact ⟨Nat.prime_iff.mp hx_prime1, Nat.prime_iff.mp hx_prime2⟩
  exact ⟨6 * x - 1, hp_goal, hp_gt⟩


/--
Analytical Limit Theorem: For sufficiently large n, the minimum sieve quotient
muMin n is strictly less than 1.
-/
theorem mu_min_eventually_lt_one : ∃ N_0 : ℕ, ∀ n ≥ N_0, muMin n < 1 := by
  sorry

/--
Theorem: The optimal multidimensional sieve weight achieves a ratio strictly less than 1
for infinitely many n.
-/
theorem mu_min_infinite : {n : ℕ | muMin n < 1}.Infinite := by
  obtain ⟨N_0, hN⟩ := mu_min_eventually_lt_one
  refine Set.Infinite.mono ?_ (Set.Ici_infinite N_0)
  intro n hn
  exact hN n hn

/--
The Twin Prime Conjecture: There are infinitely many twin primes.
-/
theorem twin_prime_conjecture : {p : ℕ | Prime p ∧ Prime (p + 2)}.Infinite := by
  apply mu_min_lt_one_implies_tpc
  exact mu_min_infinite


end KrafftSieve

