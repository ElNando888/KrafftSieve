import numpy as np
import scipy.linalg as la
import math
import argparse
import csv
import sys

def is_prime(k):
    if k < 2: return False
    if k in (2, 3): return True
    if k % 2 == 0 or k % 3 == 0: return False
    for i in range(5, int(math.isqrt(k)) + 1, 6):
        if k % i == 0 or k % (i + 2) == 0:
            return False
    return True

def get_P_n(n):
    return [p for p in range(5, 6 * n + 2) if is_prime(p)]

def get_A_n_bounds(n):
    return 6 * n**2 - 2 * n, 6 * n**2 + 10 * n + 3

def compute_c_vectorized(interval, primes):
    c_vals = np.zeros(len(interval), dtype=float)
    for p in primes:
        hit = ((6 * interval - 1) % p == 0) | ((6 * interval + 1) % p == 0)
        c_vals += hit.astype(float)
    return c_vals

def assemble_kernel_matrix(interval, primes, k=None):
    N = len(interval)
    w = len(primes)
    x_vals = interval.reshape(-1, 1)
    p_vals = np.array(primes).reshape(1, -1)
    cos_table = np.cos(6 * np.pi * x_vals / p_vals)
    
    if k is None or k >= w:
        a = cos_table[:, None, :] * cos_table[None, :, :]
        K = np.prod(1.0 + a, axis=2)
    else:
        dp = np.zeros((N, N, k + 1), dtype=float)
        dp[:, :, 0] = 1.0
        for i in range(w):
            a_i = cos_table[:, None, i] * cos_table[None, :, i]
            for j in range(k, 0, -1):
                dp[:, :, j] += a_i * dp[:, :, j - 1]
        K = np.sum(dp, axis=2)
    return K, cos_table

def solve_dual_eigenproblem(K, c_vals, tol=1e-12):
    s, U = la.eigh(K)
    s = s[::-1]
    U = U[:, ::-1]
    rank_tol = s[0] * tol
    r = np.sum(s > rank_tol)
    if r == 0:
        return 0.0, 0, None, None, None
    U_r = U[:, :r]
    tilde_C = U_r.T @ (c_vals[:, None] * U_r)
    eigenvalues, eigenvectors = la.eigh(tilde_C)
    mu_min = eigenvalues[0]
    
    v_opt = eigenvectors[:, 0]
    P_opt = U_r @ v_opt
    alpha = U_r @ (v_opt / s[:r])
    return mu_min, r, P_opt, alpha, s[:r]

def main(n, k_depth=3, max_display=100, csv_output=False):
    primes = get_P_n(n)
    lower, upper = get_A_n_bounds(n)
    interval = np.arange(lower, upper + 1)
    w = len(primes)
    
    if not csv_output:
        print(f"==================================================")
        print(f"Krafft Sieve Active Prime Analysis (n={n}, k={k_depth})")
        print(f"==================================================")
        print(f"Primes in window P_n (w={w}): {primes}")
        print(f"Interval A_n (N={len(interval)}): [{lower}, {upper}]")
        print(f"--------------------------------------------------")
    
    K, cos_table = assemble_kernel_matrix(interval, primes, k_depth)
    c_vals = compute_c_vectorized(interval, primes)
    
    mu_min, r, P_opt, alpha, s_r = solve_dual_eigenproblem(K, c_vals)
    
    if not csv_output:
        print(f"mu_min: {mu_min:.6f}, rank: {r}/{len(interval)}")
        print("Computing subset coefficients...")
    
    coeffs = []
    
    # Compute 1D, 2D, 3D based on k_depth
    # We will only go up to k=3 to keep extraction fast, even if k_depth > 3
    extract_k = min(k_depth, 3)
    
    for i in range(w):
        val = np.sum(alpha * cos_table[:, i])
        coeffs.append((abs(val), val, (i,), f"{primes[i]}", 1))
        
    if extract_k >= 2:
        for i in range(w):
            for j in range(i+1, w):
                val = np.sum(alpha * cos_table[:, i] * cos_table[:, j])
                coeffs.append((abs(val), val, (i, j), f"{primes[i]},{primes[j]}", 2))
                
    if extract_k >= 3:
        for i in range(w):
            for j in range(i+1, w):
                for l in range(j+1, w):
                    val = np.sum(alpha * cos_table[:, i] * cos_table[:, j] * cos_table[:, l])
                    coeffs.append((abs(val), val, (i, j, l), f"{primes[i]},{primes[j]},{primes[l]}", 3))
    
    coeffs.sort(reverse=True, key=lambda x: x[0])
    
    prime_activity = np.zeros(w)
    for mag, _, idx, _, _ in coeffs:
        for p_idx in idx:
            prime_activity[p_idx] += mag
            
    activity_order = np.argsort(prime_activity)[::-1]
    
    if csv_output:
        writer = csv.writer(sys.stdout)
        # Type: "Subset" or "Prime"
        writer.writerow(["Type", "n", "k", "Rank", "MuMin", "TupleSize", "Indices", "Primes", "Weight_Magnitude", "Weight_Value", "ActivitySum"])
        
        for i in range(min(max_display, len(coeffs))):
            mag, val, idx, p_str, size = coeffs[i]
            idx_str = "; ".join(map(str, idx))
            writer.writerow(["Subset", n, k_depth, r, f"{mu_min:.6f}", size, f"({idx_str})", p_str, f"{mag:.6f}", f"{val:.6f}", ""])
            
        for i in range(min(max_display, w)):
            p_idx = activity_order[i]
            writer.writerow(["Prime", n, k_depth, r, f"{mu_min:.6f}", 1, f"({p_idx})", f"{primes[p_idx]}", "", "", f"{prime_activity[p_idx]:.6f}"])
            
    else:
        print(f"\nTop {max_display} weights:")
        for i in range(min(max_display, len(coeffs))):
            _, val, idx, p_str, _ = coeffs[i]
            print(f"Basis {idx} (Primes: {p_str}): {val:.6f}")
            
        print("\nPrime Activity (sum of absolute weights involving this prime):")
        for i in range(min(max_display, w)):
            p_idx = activity_order[i]
            print(f"Prime {primes[p_idx]} (idx {p_idx}): {prime_activity[p_idx]:.6f}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Extract Active Primes from Dual Spectral Eigenvector")
    parser.add_argument("n_val", type=int, help="Value of n")
    parser.add_argument("-k", "--depth", type=int, default=3, help="Correlation depth limit")
    parser.add_argument("--top", type=int, default=100, help="Number of top items to display")
    parser.add_argument("--csv", action="store_true", help="Output in CSV format")
    args = parser.parse_args()
    main(args.n_val, args.depth, args.top, args.csv)
