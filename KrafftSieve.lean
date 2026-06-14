/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import KrafftSieve.Defs
import KrafftSieve.Basic
import KrafftSieve.ThirdHarmonic
import KrafftSieve.Variance
import KrafftSieve.SelbergWeights
import KrafftSieve.OptimalWeights
import KrafftSieve.MainTheorem

/-!
# Krafft Sieve for Twin Primes

Source: doi:10.5281/zenodo.19763833
Authors: Fernando Portela
Status: verified
Main declarations: `resonance_lt_mainTerm`, `krafft_sieve_guarantee`, `Krafft_Sufficiency`,
  `krafft_sieve_guarantee_with_mu_min`
Tags: number-theory, twin-primes, sieve-theory, fourier-analysis
MSC: 11N05, 11N35, 11N36
-/

/-!
## Mathematical overview

This project implements a formalization of a weighted Turán Sieve approach to the
Twin Prime Conjecture, utilizing the Krafft Geometry.

### Main Results

The formalization culminates in establishing the sufficiency conditions for the Krafft Sieve
to guarantee the existence of Twin Primes. The ultimate results are captured by:
* `krafft_sieve_guarantee_with_mu_min`: The Krafft Sieve Guarantee holds if $\mu_{min}(n) < 1$.
* `krafft_sieve_guarantee`: A generic formulation proving that the existence of a valid weight
  function satisfying the variance constraints guarantees the discovery of Twin Primes.
* `Krafft_Sufficiency`: Defines the exact set of conditions for the sieve to be considered
  successful.
* `resonance_lt_mainTerm`: Establishes the core inequality where the main term dominates the
  error/resonance terms.

### Major Analytical Building Blocks

To reach the main results, several key analytical and structural theorems are developed:
* `third_harmonic_extraction`: Extracts the critical third harmonic frequency from the Fourier
  domain analysis of the weighted hit counts.
* `parseval_identity`: Links the variance of the survivor distribution strictly to the sum of
  the squared magnitudes of its non-zero Fourier coefficients.
* `W_truly_multi`: Constructs the multi-dimensional optimal weight function crucial for driving
  down the physical variance.
-/
