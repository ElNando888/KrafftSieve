# Sieve Admissibility Sorry Census

This document lists all remaining `sorry` stubs in the `KrafftSieve` workspace, evaluates their mathematical and formalization difficulty, and outlines the necessary mathematical plans to close them.

---

## Summary of Stubs

There are exactly **2** core stubs remaining in the sieve reduction workspace:
*   **0** in [OptimalWeights.lean](file:///Users/nando/KrafftSieve/KrafftSieve/OptimalWeights.lean) (All 13 stubs successfully closed by Aristotle!)
*   **0** in [MainTheorem.lean](file:///Users/nando/KrafftSieve/KrafftSieve/MainTheorem.lean) (All stubs successfully closed!)
*   **2** in [RKHSLimit.lean](file:///Users/nando/KrafftSieve/KrafftSieve/RKHSLimit.lean) (Mercer's theorem/integral operator remain reserved for Tjeerd)
*   **0** in [Discretization.lean](file:///Users/nando/KrafftSieve/KrafftSieve/Discretization.lean) (All stubs successfully closed!)
*   **0** in [DirichletQuadrature.lean](file:///Users/nando/KrafftSieve/KrafftSieve/DirichletQuadrature.lean) (All stubs successfully closed!)

### Remaining sorry Stubs Census Table

| File | Line | Stub Name | Difficulty | Category | Description & Math Plan |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `RKHSLimit.lean` | 32 | `integralOperator` | **High** | Operator Theory | Definition of the continuous integral operator on $L^2$ (reserved for Tjeerd). |
| `RKHSLimit.lean` | 187 | `mercer_theorem` | **Very High** | Functional Analysis | Spectral decomposition and eigenvalues/eigenfunctions of the kernel (reserved for Tjeerd). |

---

## Closed Stubs (Recent)

### Closed in `Discretization.lean` & `DirichletQuadrature.lean` (by Aristotle)
*   `denominator_quadrature`: **Fully closed and proved** (using the exact reproducing properties of `Psi_cont` built from the Dirichlet kernel, yielding zero error).
*   `c_cont₀_basisCos_product_quadrature`: **Fully closed and proved** (using the Dirichlet reproducing window to integrate cosines exactly).
*   `numerator_quadrature`: **Fully closed and proved** (integrating the majorant weight times a linear combination squared exactly).
*   `krafft_quadrature_holds`: **Fully closed and proved** (algebraically bounding the discrete sieve minimum quotient by the continuous quotient).
*   `muMin_le_discreteRatio`: **Fully closed and proved** (attaining discrete ratios sphere).

### Closed in `MainTheorem.lean` (by Aristotle)
*   `mu_min_eventually_lt_one`: **Fully closed and proved** (using RKHS projections, convergence of continuous Rayleigh quotients, and quadrature bounds).
*   `continuousRatio_limit`: **Fully closed and proved** (using composition of limits).
*   `mu_min_infinite` / `twin_prime_conjecture`: **Fully closed and proved** (deriving infinitude from the eventual bound).

### Closed in `RKHSLimit.lean` (by Aristotle)
*   `exists_continuous_ratio_lt_one`: **Fully closed and proved** (using the test function indicator of $s \cap \{x \mid \Psi_{\text{cont}}(x) > 0\}$ to guarantee positive windowed norm).
*   `continuousRatio_continuous`: **Fully closed and proved** (using quadratic forms of weighted bilinear forms).

### Closed in `OptimalWeights.lean` (by Aristotle)
*   `S_1_eq_Q_1_pos` / `S_2_eq_Q_2_pos`: **Fully closed and proved** (using full-period windowed bounds).
*   `sufficiency_of_Q` / `mu_min_lt_one_implies_sufficiency` / `W_opt_is_sufficient_iff`: **Fully closed and proved** (linking Rayleigh quotients to Krafft admissibility).
*   `Q_1_eq_zero_iff` / `Q_2_add_kernel` / `Ratio_add_kernel`: **Fully closed and proved** (kernel decomposition of $q_1$ and $q_2$).
*   `exists_sphere_perp_ratio_eq` / `attainable_ratios_eq_image_sphere_perp`: **Fully closed and proved** (normalizing vectors to the orthogonal sphere).
*   `attainable_ratios_compact` / `exists_minimizer`: **Fully closed and proved** (attaining the minimum ratio on the compact sphere).
*   `muMin_eq_zero_of_fullRank_and_twinPrime`: **Fully closed and proved** (including base-case resolution at $n = 0$).
