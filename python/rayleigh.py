import sys
import csv
import numpy as np
import scipy.linalg as la
from multiprocessing import Pool
from itertools import combinations
import math
import argparse

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

parser = argparse.ArgumentParser("rayleigh")
parser.add_argument("n_val", help="$n$", type=int)
parser.add_argument("--cor", default=2, type=int)
parser.add_argument("--csv", action='store_true')
parser.add_argument("--primes", default="", type=str)
args = parser.parse_args()

# --- Global Configuration for Vectorization ---
# Set n here
# n_val = 10 
n_val = args.n_val
primes = np.fromstring(args.primes, dtype=int, sep=',')
w = len(primes)
if w == 0:
    primes = get_P_n(n_val)
    w = len(primes)
interval = np.arange(6*n_val**2 - 2*n_val, 6*n_val**2 + 10*n_val + 4)
basis_sets = [()] + [(i,) for i in range(w)] + list(combinations(range(w), 2))
if args.cor > 2:
    for k in range(3, args.cor + 1):
        basis_sets += list(combinations(range(w), k))

dim = len(basis_sets)

# Pre-calculate Global Penalty Array c(x)
penalties = np.zeros(len(interval))
for i, x in enumerate(interval):
    count = 0
    for p in primes:
        # Krafft Algebraic Equivalence: x hits if p | 6x-1 or p | 6x+1
        if (6*x - 1) % p == 0 or (6*x + 1) % p == 0:
            count += 1
    penalties[i] = count

# Pre-calculate Cosine Master Table (Third Harmonic)
# Dimensions: (Number of Primes) x (Length of Interval)
x_vals = interval.reshape(1, -1)
p_vals = np.array(primes).reshape(-1, 1)
# 6*pi*x/p represents the frequency-domain resonance at the 3rd harmonic
cos_table = np.cos(6 * np.pi * x_vals / p_vals)

def build_row_vectorized(row_idx):
    """Computes a single row of Matrices A and B using vectorized dot products."""
    row_A = np.zeros(dim)
    row_B = np.zeros(dim)
    
    # 1. Generalized S_vector
    S = basis_sets[row_idx]
    S_vec = np.ones(len(interval))
    for idx in S:
        S_vec *= cos_table[idx]
        
    for col_idx in range(row_idx, dim):
        T = basis_sets[col_idx]
        
        # 2. Generalized T_vector
        T_vec = np.ones(len(interval))
        for idx in T:
            T_vec *= cos_table[idx]
            
        # 3. Inner Products using NumPy
        prod = S_vec * T_vec
        row_B[col_idx] = np.sum(prod)
        row_A[col_idx] = np.sum(prod * penalties)
        
    return row_A, row_B

if __name__ == "__main__":
    if not args.csv: print(f"Initializing Optimized Krafft Sieve (n={n_val}, dim={dim})...")
    
    # Assembly via Multiprocessing
    with Pool() as pool:
        results = pool.map(build_row_vectorized, range(dim))
    
    A = np.zeros((dim, dim))
    B = np.zeros((dim, dim))
    
    for i, (row_A, row_B) in enumerate(results):
        A[i, i:] = row_A[i:]
        B[i, i:] = row_B[i:]
        A[i:, i] = A[i, i:]
        B[i:, i] = B[i, i:]

    if not args.csv: print("Matrices assembled. Performing SVD Projection...")

    # More memory-efficient than SVD for symmetric matrices
    s, U = la.eigh(B)
    # Reverse to get descending order (like SVD)
    s = s[::-1]
    U = U[:, ::-1]

    # Use a relative tolerance to identify the kernel
    tol = s[0] * 1e-7 
    rank = np.sum(s > tol)
    
    U_red = U[:, :rank]
    S_inv_sqrt = np.diag(1.0 / np.sqrt(s[:rank]))

    # Solve Generalized Eigenvalue Problem in stable space
    A_stable = S_inv_sqrt @ U_red.T @ A @ U_red @ S_inv_sqrt
    eigenvalues, eigenvectors_reduced = la.eigh(A_stable)
    
    mu_min = eigenvalues[0]
    opt_vector = U_red @ S_inv_sqrt @ eigenvectors_reduced[:, 0]
    
    if args.csv:

        # Identify the Top 100 weights
        top_k = 100
        indices = np.argsort(np.abs(opt_vector))[::-1][:top_k]

        # Create a CSV writer that targets stdout
        writer = csv.writer(sys.stdout)

        # Output each weight as a single CSV row
        # Format: n, dim, rank, mu_min, basis_index, weight_magnitude
        for idx in indices:
            writer.writerow([
                n_val, 
                dim, 
                rank, 
                f"{mu_min:.10f}", 
                str(basis_sets[idx]).replace(",", ";"), # Semicolon to avoid CSV confusion
                f"{opt_vector[idx]:.6f}"
            ])

    else:
        print(f"\n--- Spectral Analysis (n={n_val}) ---")
        print(f"Effective Rank: {rank} / {dim}")
        print(f"Min Spectral Ratio (mu_min): {mu_min:.8f}")
        print(f"Admissible (mu_min < 1): {mu_min < 1}")
        
        print("\nTop 20 Stable Weights:")
        indices = np.argsort(np.abs(opt_vector))[::-1][:20]
        for idx in indices:
            print(f"Basis {basis_sets[idx]}: {opt_vector[idx]:.4f}")
