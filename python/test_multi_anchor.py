import numpy as np
import scipy.linalg as la
import math

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

def test_multi_anchor(n, anchor_indices):
    primes = get_P_n(n)
    lower, upper = get_A_n_bounds(n)
    interval = np.arange(lower, upper + 1)
    
    anchors = [primes[i] for i in anchor_indices]
    H = [p for i, p in enumerate(primes) if i not in anchor_indices]
    
    c_vals = compute_c_vectorized(interval, primes)
    
    Phi_list = []
    for p_A in anchors:
        B_A = np.cos(6 * np.pi * interval / p_A)
        Phi_A = np.zeros((len(interval), len(H)), dtype=float)
        for idx, p in enumerate(H):
            Phi_A[:, idx] = B_A * np.cos(6 * np.pi * interval / p)
        Phi_list.append(Phi_A)
        
    Phi = np.concatenate(Phi_list, axis=1)
    
    M = Phi.T @ Phi
    P = Phi.T @ (c_vals[:, None] * Phi)
    
    s, U = la.eigh(M)
    s = s[::-1]
    U = U[:, ::-1]
    
    tol = 1e-12 * s[0]
    r = np.sum(s > tol)
    U_r = U[:, :r]
    s_r = s[:r]
    
    inv_sqrt_s = np.diag(1.0 / np.sqrt(s_r))
    P_tilde = inv_sqrt_s @ U_r.T @ P @ U_r @ inv_sqrt_s
    
    eigenvalues, _ = la.eigh(P_tilde)
    mu_min = eigenvalues[0]
    
    print(f"n={n}, Anchors={anchors} (indices {anchor_indices})")
    print(f"Subspace Rank: {r}/{Phi.shape[1]}")
    print(f"mu_min: {mu_min:.6f}")
    return mu_min

if __name__ == "__main__":
    n = 100
    print(f"Testing Multi-Anchor Subspace for n={n}...")
    # Single best anchor
    test_multi_anchor(n, [5])
    # Two best anchors
    test_multi_anchor(n, [4, 5])
    # Three anchors
    test_multi_anchor(n, [4, 5, 6])
    # Four anchors
    test_multi_anchor(n, [4, 5, 6, 7])
    # Five anchors
    test_multi_anchor(n, [2, 4, 5, 6, 7])
