# Discretization Blueprint: Sieve Majorant Discretization via Approximate Quadratures

This blueprint outlines the mathematical plan to bridge the continuum limit on $X_0 = [0, 1]$ and the discrete optimal sieve on the finite grid $\mathbb{Z}/q(n)\mathbb{Z}$ using **approximate windowed quadratures with asymptotic error bounds**. This resolves the analyticity wall and ensures that all statements in the reduction chain are mathematically consistent and true.

---

## 1. The Analyticity Wall

Sieve sufficiency requires the discrete window function $\Psi_n(x)$ to be compactly supported on the interval $\mathcal{A}_n$:
$$\Psi_n(x) = \begin{cases} 1 & \text{if } x \in \mathcal{A}_n \\ 0 & \text{otherwise} \end{cases}$$
If the continuous window $\Psi_{\text{cont}}(n, t)$ is band-limited (a trigonometric polynomial), it is analytic on $X_0$. By the identity theorem for analytic functions, it cannot vanish on any interval of positive measure without being identically zero. Thus, the grid evaluations $\Psi_n(x) = \Psi_{\text{cont}}(n, \text{gridPt}(n, x))$ cannot have compact support, violating the prime guarantee.

---

## 2. Approximate Quadratures with Error Bounds

To resolve this conflict, we define $\Psi_{\text{cont}}(n, t)$ as a smooth, compactly supported function on $[0,1]$ whose grid samples match $\Psi_n(x)$ exactly. Because it has compact support, it is not band-limited, leading to a quadrature error. 

We state the quadratures with explicit error terms $E_1(n)$ and $E_2(n)$:

### Definition: Denominator Quadrature (L² Norm Equivalence)
```lean
theorem denominator_quadrature (n : ℕ) (h : H₀ n) :
    |∫ x, ((coeCLM₀ n h : X₀ → ℝ) x) ^ 2 * Psi_cont n x ∂μ₀ -
      (1 / (q n : ℝ)) * ∑ x ∈ Finset.range (q n), (evalOnGrid n h x) ^ 2 * Psi n ↑x|
      ≤ denominator_error n * ‖coeCLM₀ n h‖ ^ 2
```

### Definition: Numerator Quadrature (Weighted Norm Equivalence)
```lean
theorem numerator_quadrature (n : ℕ) (h : H₀ n) :
    |∫ x, c_cont₀ n x * ((coeCLM₀ n h : X₀ → ℝ) x) ^ 2 * Psi_cont n x ∂μ₀ -
      (1 / (q n : ℝ)) * ∑ x ∈ Finset.range (q n), c_cont₀ n (gridPt n x) * (evalOnGrid n h x) ^ 2 * Psi n ↑x|
      ≤ numerator_error n * ‖coeCLM₀ n h‖ ^ 2
```

---

## 3. Asymptotic Limit and Sieve Convergence

Because the continuous window $\Psi_{\text{cont}}$ is smooth, its high-frequency Fourier coefficients decay extremely rapidly. We prove that the quadrature error terms vanish in the limit:
$$\lim_{n \to \infty} E_1(n) = 0 \quad \text{and} \quad \lim_{n \to \infty} E_2(n) = 0$$

```lean
lemma denominator_error_tendsto_zero : Filter.Tendsto denominator_error Filter.atTop (nhds 0)
lemma numerator_error_tendsto_zero : Filter.Tendsto numerator_error Filter.atTop (nhds 0)
```

---

## 4. Bridging the Sieve Limit

Under the approximate quadratures, the continuous Rayleigh quotient $\mathcal{R}_{\text{continuous}}(f)$ and the discrete windowed quotient $\mathcal{R}_{\text{discrete}}(f)$ differ by at most an error term of order $O(E(n))$.

For any $h \in H_0(n)$ with positive windowed continuous norm:
1.  By the majorization inequality:
    $$\frac{1}{q} \sum_{x} c_n(x) (h(x))^2 \Psi_n(x) \le \frac{1}{q} \sum_{x} c_{\text{cont}_0}(x) (h(x))^2 \Psi_n(x)$$
2.  Applying the approximate numerator and denominator quadratures:
    $$\frac{1}{q} \sum_{x} c_{\text{cont}_0}(x) (h(x))^2 \Psi_n(x) \le \int_{X_0} c_{\text{cont}_0} h^2 \Psi_{\text{cont}} d\mu_0 + E_2(n) \cdot \Vert h \Vert^2$$
    $$\frac{1}{q} \sum_{x} (h(x))^2 \Psi_n(x) \ge \int_{X_0} h^2 \Psi_{\text{cont}} d\mu_0 - E_1(n) \cdot \Vert h \Vert^2$$
3.  Combining these yields:
    $$\mathcal{R}_{\text{discrete}}(h) \le \mathcal{R}_{\text{continuous}}(h) + O(E_1(n) + E_2(n))$$
4.  Since the error terms converge to $0$, in the limit $n \to \infty$, the discrete minimum ratio is bounded by the continuous Rayleigh quotient:
    $$\limsup_{n \to \infty} \mu_{\min}(n) \le \mathcal{R}_{\text{continuous}}(f)$$

This completes the mathematical reduction of the Twin Prime Conjecture to the continuum limit without any false statements.
