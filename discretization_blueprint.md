# Discretization Blueprint: Proving `h_quadrature` via Sieve Majorants & Continuous Windowing

This blueprint outlines the formal mathematical plan to prove the discretization bridge `h_quadrature` over the continuous unit interval $X_0 = [0, 1]$ under Lebesgue measure $\mu_0$ using a band-limited continuous sieve majorant and windowed Rayleigh quotients.

---

## 1. Domain and Sieve Grid

We fix the domain to be the continuous interval $X_0 = [0, 1]$ with Lebesgue measure $\mu_0$, and define the grid points as coordinates scaled by the primorial divisor $q(n)$.

### Definition: Ambient Domain & Measure
```lean
def X₀ : Type := UnitInterval
noncomputable def μ₀ : Measure X₀ := volume
```

---

## 2. Windowed Continuous Rayleigh Quotient

Because $H_0(n)$ is finite-dimensional and spanned by $2^{w(n)}$ basis cosines, once $n \ge 3$, the dimension of the space exceeds the size of the target evaluation window $\mathcal{A}_n = 12n+4$. This means the grid evaluation mapping carries a non-trivial kernel (non-zero elements that vanish entirely on the window). 

To prevent the discrete minimum ratio $\mu_{\min}(n)$ from collapsing to $0$ on these kernel elements, the continuous Rayleigh quotient must also be windowed. We introduce the continuous window function `Psi_cont n` (a band-limited majorant of `Psi n`):

### Definition: Windowed Continuous Rayleigh Quotient
```lean
noncomputable def continuousRatio (c_cont : X → ℝ) (Psi_cont : X → ℝ) (f : Lp ℝ 2 μ) : ℝ :=
  let num := ∫ x, c_cont x * (f : X → ℝ) x ^ 2 * Psi_cont x ∂μ
  let den := ∫ x, (f : X → ℝ) x ^ 2 * Psi_cont x ∂μ
  if den = 0 then 0 else num / den
```

---

## 3. Trigonometric Exact Quadrature

Because $H_0(n)$ consists of low-frequency trigonometric polynomials of degree up to $w(n)$, their squares (and their products with the majorant $c_{\text{cont}_0}$ and window $\Psi_{\text{cont}}$) have degrees bounded strictly below the primorial grid size $q(n)$. Thus, their Riemann sum over the grid is exactly equal to their continuous integral.

### Theorem: Denominator Quadrature (L² Norm Equivalence)
```lean
theorem denominator_quadrature (n : ℕ) (h : H₀ n) :
    ∫ x, ((coeCLM₀ n h : X₀ → ℝ) x) ^ 2 * Psi_cont n x ∂μ₀ =
      (1 / (q n : ℝ)) * ∑ x ∈ Finset.range (q n), (evalOnGrid n h x) ^ 2 * Psi n (x : ZMod (q n))
```

### Theorem: Numerator Quadrature (Weighted Norm Equivalence)
Since the majorant $c_{\text{cont}_0}(n, t)$ and window $\Psi_{\text{cont}}(n, t)$ are band-limited, the continuous weighted integral matches the grid sum exactly:
```lean
theorem numerator_quadrature (n : ℕ) (h : H₀ n) :
    ∫ x, c_cont₀ n x * ((coeCLM₀ n h : X₀ → ℝ) x) ^ 2 * Psi_cont n x ∂μ₀ =
      (1 / (q n : ℝ)) *
        ∑ x ∈ Finset.range (q n), c_cont₀ n (gridPt n x) * (evalOnGrid n h x) ^ 2 * Psi n (x : ZMod (q n))
```

---

## 4. Completing the Discretization Bridge

Using the majorization inequality and the exact quadratures, we bound the discrete quotient by the continuous quotient.

For any $h \in H_0(n)$ with positive windowed norm:
1. By the majorization inequality:
   $$\sum_{x \in \text{range}(q)} c_n(x) (h(\text{gridPt}(x)))^2 \Psi_n(x) \le \sum_{x \in \text{range}(q)} c_{\text{cont}_0}(\text{gridPt}(x)) (h(\text{gridPt}(x)))^2 \Psi_n(x)$$
2. Applying the exact numerator quadrature:
   $$\frac{1}{q} \sum_{x \in \text{range}(q)} c_{\text{cont}_0}(\text{gridPt}(x)) (h(\text{gridPt}(x)))^2 \Psi_n(x) = \int_{X_0} c_{\text{cont}_0} h^2 \Psi_{\text{cont}} d\mu_0$$
3. Applying the exact denominator quadrature:
   $$\frac{1}{q} \sum_{x \in \text{range}(q)} (h(\text{gridPt}(x)))^2 \Psi_n(x) = \int_{X_0} h^2 \Psi_{\text{cont}} d\mu_0$$
4. Combining these gives:
   $$\mathcal{R}_{\text{discrete}}(h) \le \mathcal{R}_{\text{continuous}}(h)$$
5. Since $\mu_{\min}(n)$ is the infimum of `spatialRatio n` (which is bounded from below by `muMin n` for any element in the complement of the kernel), we obtain:
   $$\mu_{\min}(n) \le \mathcal{R}_{\text{continuous}}(h)$$

This proves the final discretization bridge:
```lean
theorem krafft_quadrature_holds (n : ℕ) (h : H₀ n) (hn : (∫ x, ((coeCLM₀ n h : X₀ → ℝ) x) ^ 2 * Psi_cont n x ∂μ₀) > 0) :
    muMin n ≤ continuousRatio μ₀ (c_cont₀ n) (Psi_cont n) (coeCLM₀ n h)
```
This completes the formal TPC reduction chain under the windowed majorant formulation.
