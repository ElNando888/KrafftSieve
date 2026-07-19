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

def test_star_graph(n, anchor_idx):
    primes = get_P_n(n)
    lower, upper = get_A_n_bounds(n)
    interval = np.arange(lower, upper + 1)
    
    p_A = primes[anchor_idx]
    H = [p for i, p in enumerate(primes) if i != anchor_idx]
    
    c_vals = compute_c_vectorized(interval, primes)
    
    B_A = np.cos(6 * np.pi * interval / p_A)
    
    # Construct the Star Graph basis matrix Phi (N x (w-1))
    Phi = np.zeros((len(interval), len(H)), dtype=float)
    for idx, p in enumerate(H):
        Phi[:, idx] = B_A * np.cos(6 * np.pi * interval / p)
        
    # Mass matrix in Star Graph subspace
    M = Phi.T @ Phi
    
    # Penalty matrix in Star Graph subspace
    P = Phi.T @ (c_vals[:, None] * Phi)
    
    # Solve generalized eigenvalue problem
    # M might be singular or ill-conditioned, so we use SVD projection like in dual_spectral
    s, U = la.eigh(M)
    s = s[::-1]
    U = U[:, ::-1]
    
    tol = 1e-12 * s[0]
    r = np.sum(s > tol)
    U_r = U[:, :r]
    s_r = s[:r]
    
    # P_tilde = S^(-1/2) U_r^T P U_r S^(-1/2)
    inv_sqrt_s = np.diag(1.0 / np.sqrt(s_r))
    P_tilde = inv_sqrt_s @ U_r.T @ P @ U_r @ inv_sqrt_s
    
    eigenvalues, _ = la.eigh(P_tilde)
    mu_min = eigenvalues[0]
    
    print(f"n={n}, Anchor={p_A} (idx {anchor_idx})")
    print(f"Subspace Rank: {r}/{len(H)}")
    print(f"mu_min: {mu_min:.6f}")
    return mu_min

if __name__ == "__main__":
    n = 100
    print(f"Testing Star Graph Subspace for n={n}...")
    primes = get_P_n(n)
    w = len(primes)
    
    best_mu = float('inf')
    best_idx = -1
    
    # Sweep through all possible anchors
    for i in range(min(30, w)):
        mu = test_star_graph(n, i)
        if mu < best_mu:
            best_mu = mu
            best_idx = i
            
    print(f"\n=========================================")
    print(f"Best Anchor for n={n}: Prime {primes[best_idx]} (idx {best_idx})")
    print(f"Best mu_min: {best_mu:.6f}")
    print(f"=========================================")
