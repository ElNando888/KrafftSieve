import sys
import numpy as np
import scipy.linalg as la
import math
import argparse
import csv

def is_prime(k):
    """Simple primality test."""
    if k < 2: return False
    if k in (2, 3): return True
    if k % 2 == 0 or k % 3 == 0: return False
    for i in range(5, int(math.isqrt(k)) + 1, 6):
        if k % i == 0 or k % (i + 2) == 0:
            return False
    return True

def get_P_n(n):
    """Returns the set of primes 5 <= p < 6n + 2."""
    return [p for p in range(5, 6 * n + 2) if is_prime(p)]

def get_A_n_bounds(n):
    """Returns the inclusive lower and upper bounds of A_n."""
    return 6 * n**2 - 2 * n, 6 * n**2 + 10 * n + 3

def compute_c_vectorized(interval, primes):
    """Computes the penalty function c(x) for each x in the interval."""
    c_vals = np.zeros(len(interval), dtype=float)
    for p in primes:
        # x hits if 6x - 1 or 6x + 1 is divisible by p
        hit = ((6 * interval - 1) % p == 0) | ((6 * interval + 1) % p == 0)
        c_vals += hit.astype(float)
    return c_vals

def assemble_kernel_matrix(interval, primes, k=None):
    """
    Assembles the kernel matrix K of shape (N, N).
    If k is None, uses the full power-set basis of size 2^w.
    If k is an integer, uses the restricted correlation depth k.
    """
    N = len(interval)
    w = len(primes)
    
    # Precompute cos(6*pi*x / p) for all x in the interval and all primes
    # cos_table shape: (N, w)
    x_vals = interval.reshape(-1, 1)
    p_vals = np.array(primes).reshape(1, -1)
    cos_table = np.cos(6 * np.pi * x_vals / p_vals)
    
    if k is None or k >= w:
        # Full power-set kernel using the closed-form product formula
        # K_{x, y} = prod_{p} (1 + cos(6*pi*x/p)*cos(6*pi*y/p))
        # We can construct the 3D tensor representing a_p(x, y) = cos(6*pi*x/p)*cos(6*pi*y/p)
        # Tensor shape: (N, N, w)
        # Using broadcasting: cos_table is (N, w), so we expand to (N, 1, w) and (1, N, w)
        a = cos_table[:, None, :] * cos_table[None, :, :]
        K = np.prod(1.0 + a, axis=2)
    else:
        # Restricted correlation depth k using the Newton DP algorithm
        # dp shape: (N, N, k + 1)
        dp = np.zeros((N, N, k + 1), dtype=float)
        dp[:, :, 0] = 1.0
        
        for i in range(w):
            a_i = cos_table[:, None, i] * cos_table[None, :, i] # (N, N)
            for j in range(k, 0, -1):
                dp[:, :, j] += a_i * dp[:, :, j - 1]
                
        K = np.sum(dp, axis=2)
        
    return K

def solve_dual_eigenproblem(K, c_vals, tol=1e-12):
    """
    Solves the projected spatial eigenvalue problem:
    tilde_C = U_r^T C U_r
    where C is diagonal with c_vals, and U_r is the orthonormal basis of range(K).
    """
    # 1. Perform spectral decomposition of the kernel matrix K
    s, U = la.eigh(K)
    
    # Reverse to descending order of eigenvalues
    s = s[::-1]
    U = U[:, ::-1]
    
    # Identify the effective rank of K
    rank_tol = s[0] * tol
    r = np.sum(s > rank_tol)
    
    if r == 0:
        return 0.0, 0, None
        
    # Get the orthonormal basis for range(K)
    U_r = U[:, :r]
    
    # 2. Construct the projected penalty matrix tilde_C = U_r^T C U_r
    # Since C is diagonal, U_r^T C U_r can be computed by scaling rows of U_r
    tilde_C = U_r.T @ (c_vals[:, None] * U_r)
    
    # 3. Solve the standard eigenvalue problem for tilde_C
    eigenvalues = la.eigvalsh(tilde_C)
    mu_min = eigenvalues[0]
    
    # Reconstruct the optimal spatial polynomial values P_opt
    v_opt = U_r @ la.eigh(tilde_C)[1][:, 0]
    
    return mu_min, r, v_opt

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Krafft Sieve Dual Spatial Optimization")
    parser.add_argument("n_val", type=int, help="Value of n")
    parser.add_argument("-k", "--depth", type=int, default=None, 
                        help="Correlation depth constraint (default: full power-set basis)")
    parser.add_argument("--tol", type=float, default=1e-12, help="Rank threshold tolerance")
    parser.add_argument("--csv", action='store_true')
    args = parser.parse_args()
    
    n = args.n_val
    k = args.depth
    
    primes = get_P_n(n)
    lower, upper = get_A_n_bounds(n)
    interval = np.arange(lower, upper + 1)
    N = len(interval)
    w = len(primes)
    
    if not args.csv:
        print(f"==================================================")
        print(f"Dual Spatial Sieve Optimization (n={n})")
        print(f"==================================================")
        print(f"Primes in window P_n (w={w}): {primes}")
        print(f"Interval A_n (N={N}): [{lower}, {upper}]")
    if k is None:
        dim = 2**w
        if not args.csv: print(f"Basis size D: 2^{w} = {2**w:.4e} (Full Power-Set)")
    else:
        dim = sum(math.comb(w, j) for j in range(k + 1))
        if not args.csv:
            print(f"Correlation depth limit: {k}")
            print(f"Basis size D: {dim}")
    if not args.csv: print(f"--------------------------------------------------")
    
    # Assemble the kernel matrix K
    if not args.csv: print("Assembling kernel matrix K...", end="", flush=True)
    K = assemble_kernel_matrix(interval, primes, k)
    if not args.csv: print(" Done.")
    
    # Compute penalty function c(x)
    c_vals = compute_c_vectorized(interval, primes)
    
    # Solve the dual eigenvalue problem
    if not args.csv: print("Solving dual spatial eigenproblem...", end="", flush=True)
    mu_min, rank, P_opt = solve_dual_eigenproblem(K, c_vals, args.tol)
    if not args.csv: print(" Done.")

    if args.csv:
        # Create a CSV writer that targets stdout
        writer = csv.writer(sys.stdout)

        writer.writerow([
            n, 
            k, 
            f"{dim:.4e}",
            rank,
            N, 
            f"{mu_min:.10f}"
        ])        
    else:
        print(f"--------------------------------------------------")
        print(f"Effective Rank of K: {rank} / {N}")
        print(f"Minimum Sieve Quotient (mu_min): {mu_min:.10f}")
        print(f"Admissible (mu_min < 1): {mu_min < 1.0}")
        print(f"==================================================")
