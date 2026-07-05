# Discretization Blueprint: Proving `h_quadrature` on the Continuum (Option B)

This blueprint outlines the formal mathematical plan to prove the discretization bridge `h_quadrature` over the continuous unit circle/interval $X_0 = [0, 1]$ under Lebesgue measure $\mu_0$ using the windowed trigonometric formulation.

---

## 1. Concrete Domain and Sieve Grid

We fix the domain to be the continuous interval $X_0 = [0, 1]$ with Lebesgue measure $\mu_0$, and define the grid points as coordinates scaled by the primorial divisor $q(n)$.

### Definition: Ambient Domain & Measure
```lean
def X₀ : Type := UnitInterval
noncomputable def μ₀ : Measure X₀ := volume
```

### Definition: Window Functions
We define positive window functions representing the support window $\mathcal{A}_n$:
*   Discrete window: `Psi (n : ℕ) : ZMod (q n) → ℝ` supported on `evalInterval n`.
*   Continuous window: `Psi_cont (n : ℕ) : X₀ → ℝ` as a band-limited continuous representation.

---

## 2. RKHS Representability & Subspace Mapping

Let $H_0(n)$ be the finite-dimensional Hilbert space isomorphic to the coefficient space $\mathbb{R}^{\mathcal{P}(w_n)}$.

### Definition: Grid Evaluation / Sampling
For any $h \in H_0(n)$, we define its point values globally on the grid:
```lean
def evalOnGrid (n : ℕ) (h : H₀ n) : ℕ → ℝ :=
  fun x ↦ ⟪h, representer (gridPt n x)⟫_ℝ
```

### Theorem: Subspace Representability
Show that the grid-sampled values of any RKHS function $h \in H_0(n)$ correspond exactly to a representable sieve weight `spatialVector n λ` for some coefficient vector $\lambda$:
```lean
theorem evalOnGrid_eq_spatialVector (n : ℕ) (h : H₀ n) :
    ∃ λ : Finset (Fin (w n)) → ℝ, evalOnGrid n h = spatialVector n λ := by
  sorry
```

---

## 3. Discrete Rayleigh Quotient Minimization

Using representability and the properties of the windowed discrete optimum `muMin n`, we establish the discrete lower bound.

### Theorem: Discrete Minimization Bound
For any RKHS function $h \in H_0(n)$ whose grid norm is non-zero, the discrete optimum $\mu_{\min}(n)$ is bounded by the windowed discrete Rayleigh quotient of its grid samples:
```lean
theorem muMin_le_discreteRatio (n : ℕ) (h : H₀ n)
    (h_nonZero : ∑ x ∈ evalInterval n, (evalOnGrid n h x) ^ 2 * Psi n (x : ZMod (q n)) > 0) :
    muMin n ≤ spatialRatio n (evalOnGrid n h) := by
  sorry
```

---

## 4. Trigonometric Exact Quadrature

Because $H_0(n)$ consists of trigonometric polynomials of degree up to $w(n)$, their squares (and their products with $c_{\text{cont}}$ and the band-limited window $\Psi$) have degree bounded by $2w(n) + d_{\Psi} < q(n)$. Since the primorial grid size $q(n)$ is larger than the total degree, the discrete sum matches the continuous integral exactly.

### Theorem: Denominator Quadrature (L² Norm Equivalence)
```lean
theorem denominator_quadrature (n : ℕ) (h : H₀ n) :
    ∫ x, (coeCLM₀ n h x) ^ 2 * Psi_cont n x ∂μ₀ =
      ∑ x ∈ evalInterval n, (evalOnGrid n h x) ^ 2 * Psi n (x : ZMod (q n)) := by
  sorry
```

### Theorem: Numerator Quadrature (Weighted Norm Equivalence)
```lean
theorem numerator_quadrature (n : ℕ) (h : H₀ n) :
    ∫ x, c_cont₀ x * (coeCLM₀ n h x) ^ 2 * Psi_cont n x ∂μ₀ =
      ∑ x ∈ evalInterval n, c n (x : ZMod (q n)) * (evalOnGrid n h x) ^ 2 * Psi n (x : ZMod (q n)) := by
  sorry
```

---

## 5. Completing the Discretization Bridge

Combining the discrete minimization bound with the exact windowed quadrature theorems, we prove that the discrete optimum is bounded by the continuous windowed Rayleigh quotient:

```lean
omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] in
theorem krafft_quadrature_holds (n : ℕ) (h : H₀ n) (hn : ‖coeCLM₀ n h‖ > 0) :
    muMin n ≤ continuousRatio μ₀ c_cont₀ (Psi_cont n) (coeCLM₀ n h) := by
  sorry
```
This completes the formal reduction chain under Option B.
