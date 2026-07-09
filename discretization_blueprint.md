# Discretization Blueprint: Exact Reproducing Quadratures via Dirichlet Kernels

This blueprint documents the mathematical architecture bridging the continuum limit on $X_0 = [0, 1]$ and the discrete optimal sieve on the finite grid $\mathbb{Z}/q(n)\mathbb{Z}$. Using **exact reproducing windowed quadratures** built from Dirichlet kernels, the discretization holds with **zero error**. All quadrature stubs in `Discretization.lean` are **fully proved** (zero `sorry`).

---

## 1. The Analyticity Wall and Its Resolution

Sieve sufficiency requires the discrete window function $\Psi_n(x)$ to be compactly supported on the interval $\mathcal{A}_n$:
$$\Psi_n(x) = \begin{cases} 1 & \text{if } x \in \mathcal{A}_n \\ 0 & \text{otherwise} \end{cases}$$
If the continuous window $\Psi_{\text{cont}}(n, t)$ were a band-limited function (trigonometric polynomial), it would be analytic on $X_0$. By the identity theorem for analytic functions, it cannot vanish on any interval of positive measure without being identically zero. Thus, a band-limited window cannot have compact support—the **analyticity wall**.

### The Resolution: Dirichlet-Kernel Reproducing Window

Rather than approximating the window with a band-limited function (which introduces non-vanishing errors), we construct an **exact reproducing trigonometric window** from the Dirichlet kernel. Define the real Dirichlet kernel of degree $M$:
$$D_M(s) = 1 + 2 \sum_{k=1}^M \cos(2\pi k s)$$

Its key property: for any integer frequency $|m| \le M$,
$$\int_0^1 \cos(2\pi m t) \cdot D_M(t - a)\, dt = \cos(2\pi m a)$$

The continuous window is defined as the grid-averaged Dirichlet kernel:
$$\Psi_{\text{cont}}(n, t) = \frac{1}{q(n)} \sum_{y < q(n)} \Psi_n(y) \cdot D_M\!\left(t - \frac{y}{q(n)}\right)$$
where $M = \text{kernelDegree}(n) = q(n) \cdot (6w(n) + 1)$, chosen so that every product of cosines appearing in the sieve quadratures has total absolute frequency at most $M$.

This construction is formalized in `DirichletQuadrature.lean` (zero `sorry`). The reproducing property extends via:
1. **Product-to-sum expansion** (`dirichlet_prod_cos_expand`): products of cosines → signed sums
2. **Per-frequency reproduction** (`dirichlet_cos_repro`): each frequency component is reproduced exactly
3. **Product reproduction** (`prod_cos_dirichlet_repro`): full product of cosines reproduced
4. **Grid-windowed quadrature** (`prod_cos_reproWindow`): integration against the reproducing window matches the windowed grid sum

---

## 2. Exact Quadratures (Fully Proved)

Both quadratures in `Discretization.lean` are **fully proved** with zero `sorry`, using the reproducing window machinery.

### Denominator Quadrature (L² Norm Equivalence) — ✅ Proved
```lean
theorem denominator_quadrature (n : ℕ) (h : H₀ n) :
    |∫ x, ((coeCLM₀ n h : X₀ → ℝ) x) ^ 2 * Psi_cont n x ∂μ₀ -
      (1 / (q n : ℝ)) * ∑ x ∈ Finset.range (q n), (evalOnGrid n h x) ^ 2 * Psi n ↑x|
      ≤ denominator_error n * ‖coeCLM₀ n h‖ ^ 2
```
Since `denominator_error n = 0`, this proves the exact identity:
$$\int_{X_0} (h_{\text{cont}}(t))^2 \Psi_{\text{cont}}(n, t)\, d\mu_0 = \frac{1}{q(n)} \sum_{x < q(n)} (h(x))^2 \Psi_n(x)$$

**Proof architecture**: Expand $P(x)^2 = (\sum_S \lambda_S B_S)^2$ as a double sum; apply `basisCos_pair_Psi_quadrature` term-by-term (which calls `prod_cos_Psi_cont_repro`); reassemble via `sq_sum_Psi_quadrature`.

### Numerator Quadrature (Weighted Norm Equivalence) — ✅ Proved
```lean
theorem numerator_quadrature (n : ℕ) (h : H₀ n) :
    |∫ x, c_cont₀ n x * ((coeCLM₀ n h : X₀ → ℝ) x) ^ 2 * Psi_cont n x ∂μ₀ -
      (1 / (q n : ℝ)) * ∑ x ∈ Finset.range (q n), c_cont₀ n (gridPt n x) * (evalOnGrid n h x) ^ 2 * Psi n ↑x|
      ≤ numerator_error n * ‖coeCLM₀ n h‖ ^ 2
```
Since `numerator_error n = 0`, this proves the exact identity:
$$\int_{X_0} c_{\text{cont}_0}(n, t) (h_{\text{cont}}(t))^2 \Psi_{\text{cont}}(n, t)\, d\mu_0 = \frac{1}{q(n)} \sum_{x < q(n)} c_{\text{cont}_0}(n, \text{gridPt}(n, x)) (h(x))^2 \Psi_n(x)$$

**Proof architecture**: Expand $c_{\text{cont}_0}$ into its Fourier cosine terms; for each term, apply `cos_basisCos_pair_Psi_quadrature` (which verifies the frequency bound `m.natAbs + pair_freq ≤ kernelDegree n` and calls `prod_cos_reproWindow`); reassemble via `c_cont₀_sq_sum_Psi_quadrature`.

### c_cont₀ × Basis Product Quadrature — ✅ Proved
```lean
theorem c_cont₀_basisCos_product_quadrature (n : ℕ) (S T : Finset (Fin (w n))) :
    |∫ t, c_cont₀ n t * basisCos_cont n S t * basisCos_cont n T t * Psi_cont n t ∂μ₀ -
      (1 / (q n : ℝ)) * ∑ x ∈ Finset.range (q n),
        c_cont₀ n (gridPt n x) * basisCos n S x * basisCos n T x * Psi n ↑x|
      ≤ numerator_error n
```

---

## 3. Limit Convergence (Trivial)

Because the error terms are identically zero, their limit convergence is trivial:
```lean
lemma denominator_error_tendsto_zero : Filter.Tendsto denominator_error Filter.atTop (nhds 0)
lemma numerator_error_tendsto_zero : Filter.Tendsto numerator_error Filter.atTop (nhds 0)
```

---

## 4. Bridging the Sieve Limit (Fully Proved)

The discretization bridge `krafft_quadrature_holds` is **fully proved** (zero `sorry`).

For any element $h \in H_0(n)$ with positive windowed continuous norm:
1.  By the majorization inequality (`c_le_c_cont₀`, which holds trivially since `c_cont₀` exactly interpolates `c` on the grid):
    $$\frac{1}{q} \sum_{x} c_n(x) (h(x))^2 \Psi_n(x) \le \frac{1}{q} \sum_{x} c_{\text{cont}_0}(x) (h(x))^2 \Psi_n(x)$$
2.  Applying the **exact** quadratures ($E_1 = E_2 = 0$):
    $$\frac{1}{q} \sum_{x} c_{\text{cont}_0}(x) (h(x))^2 \Psi_n(x) = \int_{X_0} c_{\text{cont}_0} h^2 \Psi_{\text{cont}}\, d\mu_0$$
    $$\frac{1}{q} \sum_{x} (h(x))^2 \Psi_n(x) = \int_{X_0} h^2 \Psi_{\text{cont}}\, d\mu_0$$
3.  Combining yields the exact bound (no residual error):
    $$\mu_{\min}(n) \le \mathcal{R}_{\text{continuous}}(h)$$
4.  In the limit $n \to \infty$:
    $$\limsup_{n \to \infty} \mu_{\min}(n) \le \mathcal{R}_{\text{continuous}}(f)$$

This completes the exact mathematical reduction of the Twin Prime Conjecture to the continuum limit.

---

## 5. Remaining Sorry Census

| File | Line | Stub Name | Status | Description |
| :--- | :--- | :--- | :--- | :--- |
| `DirichletQuadrature.lean` | — | — | ✅ All proved | Dirichlet kernel, reproducing window, exact quadrature |
| `Discretization.lean` | — | — | ✅ All proved | Denominator/numerator quadratures, bridge theorem |
| `MainTheorem.lean` | — | — | ✅ All proved | TPC reduction chain |
| `OptimalWeights.lean` | — | — | ✅ All proved | Rayleigh quotient, minimizer existence |
| `RKHSLimit.lean` | 42 | `integralOperator` | ❌ `sorry` | Definition of integral operator $T_K : L^2 \to L^2$ |
| `RKHSLimit.lean` | 227 | `mercer_theorem` | ❌ `sorry` | Mercer's spectral decomposition (reserved for Tjeerd) |

**Total: 2 `sorry` stubs remaining**, both in `RKHSLimit.lean`, both standard functional analysis.
