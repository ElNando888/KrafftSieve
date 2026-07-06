# Discretization Blueprint: Proving `h_quadrature` via Sieve Majorants

This blueprint outlines the formal mathematical plan to prove the discretization bridge `h_quadrature` over the continuous unit interval $X_0 = [0, 1]$ under Lebesgue measure $\mu_0$ using a band-limited continuous sieve majorant.

---

## 1. Domain and Sieve Grid

We fix the domain to be the continuous interval $X_0 = [0, 1]$ with Lebesgue measure $\mu_0$, and define the grid points as coordinates scaled by the primorial divisor $q(n)$.

### Definition: Ambient Domain & Measure
```lean
def X₀ : Type := UnitInterval
noncomputable def μ₀ : Measure X₀ := volume
```

---

## 2. Continuous Weight and the Sieve Majorant

Because $c_n(x)$ is a discontinuous step function on the grid, its exact continuous interpolant has infinite Fourier support and aliases under any grid-point sampling. To bypass this, we formulate $c_{\text{cont}_0}(n, t)$ as a **band-limited majorant** (upper bound) of the discrete hit function on the grid.

### Theorem: Majorization Inequality
We establish that the continuous weight function $c_{\text{cont}_0}$ majorizes the discrete hit function $c_n(x)$ at all grid points:
```lean
theorem c_le_c_cont₀ (n : ℕ) (x : ℕ) :
    c n (x : ZMod (q n)) ≤ c_cont₀ n (gridPt n x)
```

---

## 3. Trigonometric Exact Quadrature

Because $H_0(n)$ consists of low-frequency trigonometric polynomials of degree up to $w(n)$, their squares (and their products with the band-limited majorant $c_{\text{cont}_0}$) have degrees bounded strictly below the primorial grid size $q(n)$. Thus, their Riemann sum over the grid is exactly equal to their continuous integral.

### Theorem: Denominator Quadrature (L² Norm Equivalence)
```lean
theorem denominator_quadrature (n : ℕ) (h : H₀ n) :
    ∫ x, ((coeCLM₀ n h : X₀ → ℝ) x) ^ 2 ∂μ₀ =
      (1 / (q n : ℝ)) * ∑ x ∈ Finset.range (q n), (evalOnGrid n h x) ^ 2
```

### Theorem: Numerator Quadrature (Weighted Norm Equivalence)
Since the majorant $c_{\text{cont}_0}(n, t)$ is band-limited, its continuous integral matches the grid sum exactly:
```lean
theorem numerator_quadrature (n : ℕ) (h : H₀ n) :
    ∫ x, c_cont₀ n x * ((coeCLM₀ n h : X₀ → ℝ) x) ^ 2 ∂μ₀ =
      (1 / (q n : ℝ)) *
        ∑ x ∈ Finset.range (q n), c_cont₀ n (gridPt n x) * (evalOnGrid n h x) ^ 2
```

---

## 4. Completing the Discretization Bridge

Using the majorization inequality and the exact quadratures, we bound the discrete quotient by the continuous quotient.

For any $h \in H_0(n)$ with positive norm:
1. By the majorization inequality:
   $$\sum_{x \in \text{range}(q)} c_n(x) (h(\text{gridPt}(x)))^2 \le \sum_{x \in \text{range}(q)} c_{\text{cont}_0}(\text{gridPt}(x)) (h(\text{gridPt}(x)))^2$$
2. Applying the exact numerator quadrature:
   $$\frac{1}{q} \sum_{x \in \text{range}(q)} c_{\text{cont}_0}(\text{gridPt}(x)) (h(\text{gridPt}(x)))^2 = \int_{X_0} c_{\text{cont}_0} h^2 d\mu_0$$
3. Applying the exact denominator quadrature:
   $$\frac{1}{q} \sum_{x \in \text{range}(q)} (h(\text{gridPt}(x)))^2 = \int_{X_0} h^2 d\mu_0$$
4. Combining these gives:
   $$\mathcal{R}_{\text{discrete}}(h) \le \mathcal{R}_{\text{continuous}}(h)$$
5. Since $\mu_{\min}(n)$ is the minimum discrete quotient, we obtain:
   $$\mu_{\min}(n) \le \mathcal{R}_{\text{continuous}}(h)$$

This proves the final discretization bridge:
```lean
theorem krafft_quadrature_holds (n : ℕ) (h : H₀ n) (hn : ‖coeCLM₀ n h‖ > 0) :
    muMin n ≤ continuousRatio μ₀ (c_cont₀ n) (coeCLM₀ n h)
```
This completes the formal TPC reduction chain under the majorant formulation.
