import math

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

def get_q_n(primes):
    """Calculates the primorial q_n."""
    q = 1
    for p in primes:
        q *= p
    return q

def r_K(p):
    """The Krafft residue choice: r_K = floor((p+1)/6)."""
    return (p + 1) // 6

def get_A_n_bounds(n):
    """Returns the inclusive lower and upper bounds of A_n."""
    return 6 * n**2 - 2 * n, 6 * n**2 + 10 * n + 3

def c(x, primes):
    """The global hit counter: tallies physical collisions with the Krafft residues."""
    hits = 0
    for p in primes:
        r = r_K(p)
        mod_x = x % p
        if mod_x == r or mod_x == (p - r) % p:
            hits += 1
    return hits

def weight(n, x, lower_bound, upper_bound, primes, alpha, nconv=2, use_log_weight=True):
    """
    The Analytic Sieve Weight: Continuous, Smooth, and Non-Negative.
    Mimics the GPY/Selberg multidimensional tuning in a 1D continuous wave.
    """
    # 1. The Base Bump (Low-Pass Filter)
    center = (lower_bound + upper_bound) / 2.0
    radius = (upper_bound - lower_bound) / 2.0
    dist = (x - center) / radius
    
    # Compact support: strictly zero outside the interval
    if abs(dist) >= 1.0:
        return 0.0
        
    # Smooth, 4th-order bell-like bump
    bump = (1.0 - dist**2)**4 
    
    # 2. The Cosine Resonator (Amplitude Modulation)
    penalty_sum = 0.0
    k = 3.0 # The Krafft 3rd Harmonic
    
    for p in primes:
        r = r_K(p)
        
        # Continuous wave that peaks at the forbidden residues
        spatial_wave = 2.0 * math.cos(2 * math.pi * k * x / p) * math.cos(2 * math.pi * k * r / p)
        
        # Logarithmic decay to penalize small primes more heavily
        if use_log_weight:
            lam = math.log(upper_bound / p) / p 
        else:
            lam = 1.0 / p
            
        penalty_sum += lam * spatial_wave
        
    # 3. The Selberg/GPY Squaring
    # Guarantees non-negativity and mathematically forces the high-frequency spikes
    # (modified to allow for higher exponents)
    resonator = abs((1.0 - alpha * penalty_sum)**nconv)
    
    return bump * resonator

def run_test(nconv=2):
    """Sweeps through tuning parameters to find the optimal ratio of Hits to Mass."""
    print(f"{'n':<3} | {'Best Alpha':<10} | {'S1 (Mass)':<14} | {'S2 (Hits)':<14} | {'Ratio S2/S1':<14} | S2 < S1? (nconv={nconv})")
    print("-" * 80)
    
    for n in range(2, 103):
        primes = get_P_n(n)
        lower, upper = get_A_n_bounds(n)
        
        best_ratio = float('inf')
        best_alpha = 0.0
        best_S1 = 0.0
        best_S2 = 0.0
        
        # Grid search for the optimal tuning parameter 'alpha' (0.01 to 2.00)
        for alpha_step in range(1, 201):
            test_alpha = alpha_step / 100.0
            
            S1_test = 0.0
            S2_test = 0.0
            
            # Evaluate the continuous wave over the spatial interval
            for x in range(lower, upper + 1):
                w_val = weight(n, x, lower, upper, primes, test_alpha, nconv, use_log_weight=True)
                if w_val > 0:
                    c_val = c(x, primes)
                    S1_test += w_val
                    S2_test += w_val * c_val
                    
            if S1_test > 0:
                ratio = S2_test / S1_test
                if ratio < best_ratio:
                    best_ratio = ratio
                    best_alpha = test_alpha
                    best_S1 = S1_test
                    best_S2 = S2_test
                    
        success = best_S2 < best_S1
        s1 = f"{best_S1:.8e}" if best_S1 > 10000000 else f"{best_S1:<14.4f}"
        s2 = f"{best_S2:.8e}" if best_S2 > 10000000 else f"{best_S2:<14.4f}"
        print(f"{n:<3} | {best_alpha:<10.3f} | {s1} | {s2} | {best_ratio:<14.4f} | {success}", flush=True)

if __name__ == '__main__':
    for nconv in range(2, 20):
        run_test(nconv)

