import math
import numpy as np
from concurrent.futures import ProcessPoolExecutor

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

def r_K(p):
    """The Krafft residue choice: r_K = floor((p+1)/6)."""
    return (p + 1) // 6

def c_vectorized(x_range, primes):
    """Calculates hits for a range of x values using NumPy."""
    hits = np.zeros(len(x_range), dtype=int)
    for p in primes:
        r = r_K(p)
        mod_x = x_range % p
        hits += (mod_x == r) | (mod_x == (p - r) % p)
    return hits

def weight_vectorized(n, x_range, lower, upper, primes, alpha, nconv=2):
    """Vectorized version of the Analytic Sieve Weight."""
    center = (lower + upper) / 2.0
    radius = (upper - lower) / 2.0
    dist = (x_range - center) / radius
    
    # Base Bump
    bump = np.where(np.abs(dist) < 1.0, (1.0 - dist**2)**4, 0.0)

    # Cosine Resonator
    penalty_sum = np.zeros(len(x_range))
    k = 3.0
    for p in primes:
        r = r_K(p)
        # Using the product-to-sum identity logic from original script
        spatial_wave = 3.0 * np.cos(2 * np.pi * k * x_range / p) * math.cos(2 * np.pi * k * r / p)
        penalty_sum += (1.0 / p) * spatial_wave
        
    resonator = np.abs((1.0 - alpha * penalty_sum))**nconv
    return bump * resonator

def evaluate_alpha(alpha_step, n, x_range, lower, upper, primes, nconv, c_vals):
    """Worker function to evaluate a single alpha value."""
    test_alpha = alpha_step / 100.0
    w_vals = weight_vectorized(n, x_range, lower, upper, primes, test_alpha, nconv)
    
    s1 = np.sum(w_vals)
    if s1 > 0:
        s2 = np.sum(w_vals * c_vals)
        return (s2 / s1, test_alpha, w_vals, s1, s2)
    return (float('inf'), test_alpha, None, 0, 0)

def run_test(nconv, results_store):
    print(f"\n--- Running nconv={nconv} (Parallel Alpha Search) ---")
    print(f"{'n':<3} | {'Best Alpha':<10} | {'S1 (Mass)':<14} | {'S2 (Hits)':<14} | {'Ratio':<10} | Success")
    print("-" * 85)
    
    limit = math.floor(math.exp((nconv + 2.65) / 2.05)) + 1
    alpha_steps = list(range(115, 441, 2))

    for n in range(2, limit):
        if n in results_store:
            v = results_store[n][0]
            print(f"{n:<3} | {'-':<10} | {'-':<14} | {'-':<14} | {'-':<10} | True ({v[0]}, {v[2]:<6.3f})", flush=True)
            continue        
            
        primes = get_P_n(n)
        lower, upper = get_A_n_bounds(n)
        x_range = np.arange(lower, upper + 1)
        c_vals = c_vectorized(x_range, primes)
        
        # Parallelize the alpha loop
        best_ratio = float('inf')
        best_alpha = 0.0
        best_weights = None
        best_stats = (0, 0)

        with ProcessPoolExecutor() as executor:
            # Map the alpha steps to the worker function
            futures = [executor.submit(evaluate_alpha, a, n, x_range, lower, upper, primes, nconv, c_vals) for a in alpha_steps]
            
            for future in futures:
                ratio, test_alpha, w_vals, s1, s2 = future.result()
                if ratio < best_ratio:
                    best_ratio = ratio
                    best_alpha = test_alpha
                    best_weights = w_vals
                    best_stats = (s1, s2)
        
        success = best_stats[1] < best_stats[0]
        if success:
            if n not in results_store:
                results_store[n] = []
            results_store[n].append((nconv, best_weights, best_alpha))
            
        s1_str = f"{best_stats[0]:.4e}" if best_stats[0] > 1e6 else f"{best_stats[0]:.4f}"
        s2_str = f"{best_stats[1]:.4e}" if best_stats[1] > 1e6 else f"{best_stats[1]:.4f}"
        print(f"{n:<3} | {best_alpha:<10.3f} | {s1_str:<14} | {s2_str:<14} | {best_ratio:<10.4f} | {success}", flush=True)

if __name__ == '__main__':
    # Key: n, Value: list of (nconv, weights)
    results_store = {}
    
    for nconv in range(2, 13):
        run_test(nconv, results_store)

    """
    print("\n" + "="*50)
    print("FINAL WEIGHTS REPORT (GROUPED BY n)")
    print("="*50)
    
    for n in sorted(results_store.keys()):
        print(f"\n[n = {n}]")
        for nconv, weights in results_store[n]:
            # Showing a slice or stats to keep output readable; 
            # change to 'print(weights)' to see every single value
            print(f"  -> nconv {nconv}: {len(weights)} weights stored. (Sum: {np.sum(weights):.4f}, Max: {np.max(weights):.4f})")
            # To see the raw list of weights, uncomment the line below:
            print(f"     Weights: {weights.tolist()}")
    """
