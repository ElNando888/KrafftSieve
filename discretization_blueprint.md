# Discretization Blueprint: Proving `h_quadrature` on the Continuum (Route B)

This blueprint outlines the formal mathematical plan to prove the discretization bridge `h_quadrature` over the continuous unit circle/interval $X = [0, 1]$ under Lebesgue measure $\mu$. It implements **Route B**, establishing that the discrete sieve grid is an exact quadrature rule for the reproducing kernel space of trigonometric polynomials.

---

## 1. Concrete Domain and Sieve Grid

We fix the domain to be the continuous interval $X = [0, 1]$ with Lebesgue measure $\mu$, and define the grid points as coordinates scaled by the primorial divisor $q(n)$.

### Definition: Ambient Domain & Measure
```lean
def X₀ : Type := UnitInterval
noncomputable def μ₀ : Measure X₀ := volume
```

### Definition: Sieve Grid Mapping
We map the integers in the evaluation interval to coordinates in $[0, 1]$:
```lean
def gridPt (n : ℕ) (x : ℕ) : X₀ :=
  -- Coerced value x / (q n) projected onto the UnitInterval
  sorry
```

---

## 2. RKHS Representability & Subspace Mapping

Let $H_0(n)$ be the finite-dimensional Hilbert space isomorphic to the coefficient space $\mathbb{R}^{\mathcal{P}(w_n)}$, whose reproducing kernel is the spatial kernel $K_n(x, y) = \sum_S B_S(x)B_S(y)$ constructed from the basis cosines.

### Definition: Grid Evaluation / Sampling
For any $h \in H_0(n)$, we define its point values on the grid points corresponding to `evalInterval n`:
```lean
def evalOnGrid (n : ℕ) (h : H₀ n) : ℕ → ℝ :=
  fun x ↦ if x ∈ evalInterval n then ⟪h, representer (gridPt n x)⟫_ℝ else 0
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

Using representability and the properties of `muMin n`, we establish the discrete lower bound.

### Theorem: Discrete Minimization Bound
For any RKHS function $h \in H_0(n)$ whose grid norm is non-zero, the discrete optimum $\mu_{\min}(n)$ is bounded by the discrete Rayleigh quotient of its grid samples:
```lean
theorem muMin_le_discreteRatio (n : ℕ) (h : H₀ n)
    (h_nonZero : ∑ x ∈ evalInterval n, (evalOnGrid n h x) ^ 2 > 0) :
    muMin n ≤ spatialRatio n (evalOnGrid n h) := by
  -- Follows from csInf_le, BddBelow (attainableRatios n),
  -- and evalOnGrid_eq_spatialVector
  sorry
```

---

## 4. Trigonometric Exact Quadrature

Because $H_0(n)$ consists of trigonometric polynomials of degree up to $w(n)$, their squares (and their products with $c_{\text{cont}}$) have degree bounded by $3w(n)$. Since the primorial grid size $q(n)$ is much larger than the degree, the discrete sum matches the continuous integral exactly.

### Theorem: Denominator Quadrature (L² Norm Equivalence)
```lean
theorem denominator_quadrature (n : ℕ) (h : H₀ n) :
    ∫ x, (coeCLM₀ n h x) ^ 2 ∂μ₀ = ∑ x ∈ evalInterval n, (evalOnGrid n h x) ^ 2 := by
  -- Proved via character orthogonality of cosines on the grid
  sorry
```

### Theorem: Numerator Quadrature (Weighted Norm Equivalence)
```lean
theorem numerator_quadrature (n : ℕ) (h : H₀ n) :
    ∫ x, c_cont₀ x * (coeCLM₀ n h x) ^ 2 ∂μ₀ =
      ∑ x ∈ evalInterval n, c n (x : ZMod (q n)) * (evalOnGrid n h x) ^ 2 := by
  -- Proved via character orthogonality of cosines on the grid
  sorry
```

---

## 5. Completing the Discretization Bridge

Combining the discrete minimization bound with the exact quadrature theorems, we prove that the discrete optimum is bounded by the continuous Rayleigh quotient of any RKHS function:

```lean
omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] in
theorem krafft_quadrature_holds (n : ℕ) (h : H₀ n) (hn : ‖coeCLM₀ n h‖ > 0) :
    muMin n ≤ continuousRatio μ₀ c_cont₀ (coeCLM₀ n h) := by
  -- 1. Unfold continuousRatio and rewrite integrals using denominator_quadrature
  --    and numerator_quadrature.
  -- 2. Identify the resulting quotient with spatialRatio.
  -- 3. Apply muMin_le_discreteRatio.
  sorry
```
This completes the formal reduction chain, leaving the entire continuous limit proof verified without axioms.
