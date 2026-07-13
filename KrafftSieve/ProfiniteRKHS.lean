import Mathlib
import KrafftSieve.Defs

/-!
# Profinite RKHS Refactor

This file refactors the RKHS ambient space `X` of the Krafft Sieve so that the
finite-dimensional RKHS spaces are genuinely nested.

Instead of scaling the domain `[0,1]` (which makes the nesting hypothesis `h_mono`
mathematically false, because the frequencies scale by `p_{w+1}` at each step), we
place the *unscaled* periodic basis functions on their natural compact ambient space:
the countable product of the finite cyclic groups `ZMod pᵢ` (a model of the profinite
integers restricted to the primes used in the sieve).

* `X` — the ambient space `Π i, ZMod (globalPrime i)`, a compact Hausdorff group.
* `haarProb` — the normalized Haar (product-of-uniform) probability measure on `X`.
* `charFun k` / `charLp k` — the (unscaled) character basis functions, as continuous
  functions and as elements of `L²(X, haarProb)`.
* `H n` — the finite-dimensional span of the characters whose frequencies live in the
  `n`-th prime window, a submodule of `L²(X, haarProb)`.
* `H_mono` — the structural nesting `H n ≤ H (n+1)` (this is the `h_mono` hypothesis
  of `KrafftSieve.projection_strong_convergence`).
* `H_dense` — density of `⨆ n, H n` (the `h_dense` hypothesis); Peter–Weyl.

Both `H_mono` (structural nesting) and `H_dense` (Peter–Weyl / Stone–Weierstrass together
with density of continuous functions in `L²`) are proved here with no `sorry`. The remaining
task 6 of the provided solution (identifying the exact Dirichlet quadrature with the Haar
integral over `X`) belongs to `DirichletQuadrature.lean` and is not addressed in this file.
-/

namespace KrafftSieve

open MeasureTheory TopologicalSpace

/-- The i-th prime used in the global space (starts at 5, so offset by 2) -/
noncomputable def globalPrime (i : ℕ) : ℕ := Nat.nth Nat.Prime (i + 2)

/-- Each `globalPrime i` is prime. -/
lemma globalPrime_prime (i : ℕ) : (globalPrime i).Prime := Nat.prime_nth_prime _

instance (i : ℕ) : Fact (globalPrime i).Prime := ⟨globalPrime_prime i⟩

instance (i : ℕ) : NeZero (globalPrime i) := ⟨(globalPrime_prime i).pos.ne'⟩

-- Ensure ZMod p has the discrete topology and is compact
instance (i : ℕ) : TopologicalSpace (ZMod (globalPrime i)) := ⊥
instance (i : ℕ) : DiscreteTopology (ZMod (globalPrime i)) := ⟨rfl⟩

-- Give `ZMod (globalPrime i)` the discrete (⊤) measurable space and a uniform measure.
instance (i : ℕ) : MeasurableSpace (ZMod (globalPrime i)) := ⊤
instance (i : ℕ) : MeasurableSingletonClass (ZMod (globalPrime i)) := ⟨fun _ => trivial⟩
instance (i : ℕ) : BorelSpace (ZMod (globalPrime i)) := ⟨borel_eq_top_of_discrete.symm⟩

/-- A discrete finite space is compact. -/
instance (i : ℕ) : CompactSpace (ZMod (globalPrime i)) := Finite.compactSpace

/-- The uniform probability measure on the finite group `ZMod (globalPrime i)`. -/
noncomputable def unifMeasure (i : ℕ) : Measure (ZMod (globalPrime i)) :=
  (PMF.uniformOfFintype (ZMod (globalPrime i))).toMeasure

instance (i : ℕ) : IsProbabilityMeasure (unifMeasure i) := by
  unfold unifMeasure; infer_instance

/-- The ambient space X is the countable product of ZMod (globalPrime i).
    This is a compact Hausdorff topological group. -/
def X := (i : ℕ) → ZMod (globalPrime i)

instance : TopologicalSpace X := Pi.topologicalSpace
instance : CompactSpace X := Pi.compactSpace
instance : T2Space X := Pi.t2Space
instance : SecondCountableTopology X :=
  inferInstanceAs (SecondCountableTopology ((i : ℕ) → ZMod (globalPrime i)))
instance : PolishSpace X :=
  inferInstanceAs (PolishSpace ((i : ℕ) → ZMod (globalPrime i)))
instance : MeasurableSpace X :=
  inferInstanceAs (MeasurableSpace ((i : ℕ) → ZMod (globalPrime i)))
instance : BorelSpace X :=
  inferInstanceAs (BorelSpace ((i : ℕ) → ZMod (globalPrime i)))

noncomputable instance : AddCommGroup X := Pi.addCommGroup
instance : ContinuousAdd X := Pi.continuousAdd

/-- The normalized Haar probability measure on `X`, realized as the product of the
uniform probability measures on the finite factors. -/
noncomputable def haarProb : Measure X :=
  Measure.infinitePi unifMeasure

instance : IsProbabilityMeasure haarProb := by
  unfold haarProb
  exact inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi unifMeasure))

/-!
## The unscaled character basis functions
-/

/-- The unscaled character basis function attached to a finitely-supported frequency
vector `k : ℕ →₀ ℤ`:
`charFun k x = ∏ i ∈ k.support, exp(2π i · kᵢ · (xᵢ) / pᵢ)`.
These are the natural (unscaled) profinite analogues of `∏ cos(2π (3/pᵢ) x)`. -/
noncomputable def charFun (k : ℕ →₀ ℤ) (x : X) : ℂ :=
  ∏ i ∈ k.support,
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      ((k i : ℂ) * ((x i).val : ℂ) / (globalPrime i : ℂ)))

/-- The single-coordinate factor of a character, as a continuous map `ℂ → ℂ`. -/
noncomputable def charFactor (k : ℕ →₀ ℤ) (i : ℕ) (c : ℂ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k i : ℂ) * c / (globalPrime i : ℂ)))

lemma charFactor_continuous (k : ℕ →₀ ℤ) (i : ℕ) : Continuous (charFactor k i) := by
  unfold charFactor; fun_prop

/-- The coordinate-value map `x ↦ ((x i).val : ℂ)` is continuous. -/
lemma coordVal_continuous (i : ℕ) : Continuous (fun x : X => ((x i).val : ℂ)) :=
  (continuous_of_discreteTopology
    (f := fun z : ZMod (globalPrime i) => ((z.val : ℂ)))).comp (continuous_apply i)

/-- The coordinate-value map `x ↦ ((x i).val : ℂ)` is measurable. -/
lemma coordVal_measurable (i : ℕ) : Measurable (fun x : X => ((x i).val : ℂ)) :=
  (measurable_from_top (f := fun z : ZMod (globalPrime i) => ((z.val : ℂ)))).comp
    (measurable_pi_apply i)

lemma charFun_eq_prod (k : ℕ →₀ ℤ) (x : X) :
    charFun k x = ∏ i ∈ k.support, charFactor k i ((x i).val : ℂ) := rfl

/-- Each character basis function is continuous. -/
lemma charFun_continuous (k : ℕ →₀ ℤ) : Continuous (charFun k) := by
  rw [show charFun k = fun x => ∏ i ∈ k.support, charFactor k i ((x i).val : ℂ) from rfl]
  have hfac : ∀ i, Continuous (fun x : X => charFactor k i ((x i).val : ℂ)) :=
    fun i => (charFactor_continuous k i).comp (coordVal_continuous i)
  fun_prop

/-- Each character basis function is measurable. -/
lemma charFun_measurable (k : ℕ →₀ ℤ) : Measurable (charFun k) := by
  rw [show charFun k = fun x => ∏ i ∈ k.support, charFactor k i ((x i).val : ℂ) from rfl]
  have hfac : ∀ i, Measurable (fun x : X => charFactor k i ((x i).val : ℂ)) :=
    fun i => ((charFactor_continuous k i).measurable).comp (coordVal_measurable i)
  fun_prop

/-- Each factor of a character (evaluated at a real argument) has modulus one. -/
lemma charFactor_norm (k : ℕ →₀ ℤ) (i : ℕ) (c : ℂ) (hc : c.im = 0) :
    ‖charFactor k i c‖ = 1 := by
  unfold charFactor
  rw [Complex.norm_exp]
  have : (2 * (Real.pi : ℂ) * Complex.I * ((k i : ℂ) * c / (globalPrime i : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.div_re, Complex.div_im, hc]
  rw [this, Real.exp_zero]

/-- Each character has constant modulus one, hence is bounded. -/
lemma charFun_norm_le (k : ℕ →₀ ℤ) (x : X) : ‖charFun k x‖ ≤ 1 := by
  rw [charFun_eq_prod, norm_prod]
  refine Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [charFactor_norm k i _ (by simp only [Complex.natCast_im])]

/-- Each character basis function lies in `L²(X, haarProb)`. -/
lemma charFun_memLp (k : ℕ →₀ ℤ) : MemLp (charFun k) 2 haarProb := by
  have hbdd : MemLp (charFun k) ⊤ haarProb :=
    memLp_top_of_bound (charFun_measurable k).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun x => charFun_norm_le k x))
  exact hbdd.mono_exponent le_top

/-- The character basis function as an element of `L²(X, haarProb)`. -/
noncomputable def charLp (k : ℕ →₀ ℤ) : Lp ℂ 2 haarProb :=
  (charFun_memLp k).toLp _

/-- The character basis function packaged as a bundled continuous map `C(X, ℂ)`. -/
noncomputable def charMk (k : ℕ →₀ ℤ) : C(X, ℂ) := ⟨charFun k, charFun_continuous k⟩

/-- `charLp k` is the image of the bundled continuous character under `ContinuousMap.toLp`. -/
lemma charLp_eq_toLp (k : ℕ →₀ ℤ) :
    charLp k = ContinuousMap.toLp 2 haarProb ℂ (charMk k) := by
  apply Lp.ext
  filter_upwards [(charFun_memLp k).coeFn_toLp,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) haarProb (charMk k)] with x h1 h2
  simp only [charLp]
  rw [h1, h2]; rfl

/-- The character homomorphism law: `χ_{k₁+k₂} = χ_{k₁} · χ_{k₂}` pointwise. -/
lemma charFun_add_apply (k₁ k₂ : ℕ →₀ ℤ) (x : X) :
    charFun (k₁ + k₂) x = charFun k₁ x * charFun k₂ x := by
  unfold charFun; simp +decide [ Finsupp.support_add_eq, Finset.prod_mul_distrib ] ;
  rw [ Finset.prod_subset ( show ( k₁ + k₂ |> Finsupp.support ) ⊆ k₁.support ∪ k₂.support from fun i hi => by by_cases hi₁ : k₁ i = 0 <;> by_cases hi₂ : k₂ i = 0 <;> aesop ) ];
  · rw [ Finset.prod_subset ( show k₁.support ⊆ k₁.support ∪ k₂.support from Finset.subset_union_left ), Finset.prod_subset ( show k₂.support ⊆ k₁.support ∪ k₂.support from Finset.subset_union_right ) ];
    · rw [ ← Finset.prod_mul_distrib ] ; congr ; ext ; rw [ ← Complex.exp_add ] ; ring;
    · aesop;
    · aesop;
  · intro i hi h; norm_cast at *; aesop;

/-- The trivial character is the constant `1`. -/
lemma charFun_zero_apply (x : X) : charFun 0 x = 1 := by
  unfold charFun; aesop;

/-- The inverse character is the complex conjugate. -/
lemma charFun_neg_apply (k : ℕ →₀ ℤ) (x : X) :
    charFun (-k) x = starRingEnd ℂ (charFun k x) := by
  unfold charFun; simp +decide [ Finsupp.support_neg ] ;
  refine' Finset.prod_congr rfl fun i hi => _;
  norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, neg_div ];
  erw [ ZMod.cast_eq_val ] ; norm_cast ; aesop;

/-- The characters separate the points of the compact space `X`. -/
lemma charFun_separatesPoints : (Set.range charFun).SeparatesPoints := by
  intro x y hxy; contrapose! hxy; simp_all +decide [ funext_iff, Complex.exp_eq_exp_iff_exists_int ] ;
  -- By definition of $charFun$, if $charFun k x = charFun k y$ for all $k$, then $x_i = y_i$ for all $i$.
  have h_eq : ∀ i, (x i).val = (y i).val := by
    intro i
    specialize hxy (fun x => Complex.exp (2 * Real.pi * Complex.I * ((x i).val : ℂ) / (globalPrime i : ℂ))) (Finsupp.single i 1) (by
    unfold charFun; simp +decide [ Finsupp.single_apply ]
    intro x; rw [mul_div_assoc]);
    rw [ Complex.exp_eq_exp_iff_exists_int ] at hxy;
    -- By simplifying, we can see that $(x_i).val = (y_i).val$.
    obtain ⟨n, hn⟩ := hxy
    have h_eq : (x i).val = (y i).val + n * (globalPrime i) := by
      rw [ div_add', div_eq_div_iff ] at hn <;> norm_num [ Complex.ext_iff, Real.pi_ne_zero, Nat.Prime.ne_zero ( globalPrime_prime i ) ] at *;
      erw [ ZMod.cast_eq_val, ZMod.cast_eq_val ] at * ; norm_cast at *;
      exact_mod_cast ( by nlinarith [ Real.pi_pos ] : ( x i |> ZMod.val : ℝ ) = ( y i |> ZMod.val : ℝ ) + n * ( globalPrime i : ℝ ) );
    nlinarith [ show n = 0 by nlinarith [ ZMod.val_lt ( x i ), ZMod.val_lt ( y i ) ] ];
  exact funext fun i => ZMod.val_injective _ <| h_eq i

/-!
## The nested finite-dimensional RKHS spaces
-/

/-- The set of coordinate indices whose prime lies in the `n`-th prime window,
i.e. `{ i | globalPrime i < 6n + 2 }`. As `n` grows this set only grows. -/
def indexWindow (n : ℕ) : Set ℕ := {i | globalPrime i < 6 * n + 2}

/-- The set of frequency vectors supported on the `n`-th index window. -/
def freqSet (n : ℕ) : Set (ℕ →₀ ℤ) := {k | (↑k.support : Set ℕ) ⊆ indexWindow n}

/-- The set of character basis functions with frequencies in the `n`-th window. -/
noncomputable def basisSet (n : ℕ) : Set (Lp ℂ 2 haarProb) := charLp '' freqSet n

/-- `H n` is the finite-window span of the character basis functions inside `L²(X)`. -/
noncomputable def H (n : ℕ) : Submodule ℂ (Lp ℂ 2 haarProb) :=
  Submodule.span ℂ (basisSet n)

/-- The index windows are monotone in `n`. -/
lemma indexWindow_mono {m n : ℕ} (h : m ≤ n) : indexWindow m ⊆ indexWindow n := by
  intro i hi
  simp only [indexWindow, Set.mem_setOf_eq] at hi ⊢
  omega

/-- The frequency sets are monotone in `n`. -/
lemma freqSet_mono {m n : ℕ} (h : m ≤ n) : freqSet m ⊆ freqSet n :=
  fun _ hk => Set.Subset.trans hk (indexWindow_mono h)

/-- The basis sets are monotone in `n`. -/
lemma basisSet_mono {m n : ℕ} (h : m ≤ n) : basisSet m ⊆ basisSet n :=
  Set.image_mono (freqSet_mono h)

/-- **`h_mono`**: the finite-dimensional RKHS spaces are strictly nested; as submodules
of the same `L²(X)` the inclusion `H m ↪ H n` (for `m ≤ n`) is an isometry. -/
theorem H_mono : Monotone H :=
  fun _ _ h => Submodule.span_mono (basisSet_mono h)

/-- The `h_mono` hypothesis of `projection_strong_convergence`, in its inclusion form:
every element of `H i` is (as an element of `L²(X)`) also an element of `H j` for `i ≤ j`. -/
theorem H_incl (i j : ℕ) (hij : i ≤ j) (x : H i) :
    ∃ y : H j, (x : Lp ℂ 2 haarProb) = (y : Lp ℂ 2 haarProb) :=
  ⟨⟨(x : Lp ℂ 2 haarProb), H_mono hij x.2⟩, rfl⟩

/-- The set of all character basis functions in `L²(X)`. -/
noncomputable def charSet : Set (Lp ℂ 2 haarProb) := Set.range charLp

/-- Every frequency vector eventually lies in some window: the windows exhaust `ℕ →₀ ℤ`. -/
lemma iUnion_freqSet : (⋃ n, freqSet n) = Set.univ := by
  ext k
  simp only [Set.mem_iUnion, freqSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  refine ⟨k.support.sup globalPrime, fun i hi => ?_⟩
  have h := Finset.le_sup (f := globalPrime) hi
  simp only [indexWindow, Set.mem_setOf_eq]
  omega

/-- The union of the windowed basis sets is the full set of characters. -/
lemma iUnion_basisSet : (⋃ n, basisSet n) = charSet := by
  simp only [basisSet, charSet, ← Set.image_iUnion, iUnion_freqSet, Set.image_univ]

/-- The union of the finite-window spans is exactly the span of the full character system.
This is the structural bridge between the windowed construction and Peter–Weyl. -/
lemma iSup_H_eq : (⨆ n, H n) = Submodule.span ℂ charSet := by
  simp only [H, ← Submodule.span_iUnion, iUnion_basisSet]

/-- **Density of the character span** (Peter–Weyl for the compact abelian group `X`).

The linear span of the characters `charLp k` is dense in `L²(X, haarProb)`. The proof:
(i) the characters generate a `*`-subalgebra of `C(X, ℂ)` (closed under products,
`charFun k₁ * charFun k₂ = charFun (k₁ + k₂)`, containing the constant `charFun 0 = 1`,
and closed under conjugation, `conj (charFun k) = charFun (-k)`); (ii) this subalgebra
separates the points of the compact Hausdorff space `X` (distinct points differ in some
coordinate `i`, distinguished by `charFun (Finsupp.single i 1)`); (iii) by the complex
Stone–Weierstrass theorem it is uniformly dense in `C(X, ℂ)`; (iv) `C(X, ℂ)` is dense in
`L²(X, haarProb)` (`ContinuousMap.toLp_denseRange`, since `haarProb` is a finite Borel
measure on the compact Polish space `X`); combining these gives density in `L²`. -/
theorem charSpan_dense : (Submodule.span ℂ charSet).topologicalClosure = ⊤ := by
  -- The span of the characters in $L^2(X)$ is dense by the Stone-Weierstrass theorem because the characters form a *-subalgebra of $C(X, \mathbb{C})$ that separates points and contains the constant functions.
  have h_span_dense : ∀ f : C(X, ℂ), ∃ seq : ℕ → Lp ℂ 2 haarProb, Filter.Tendsto seq Filter.atTop (nhds (ContinuousMap.toLp 2 haarProb ℂ f)) ∧ ∀ n, seq n ∈ Submodule.span ℂ (Set.range charLp) := by
    intro f
    obtain ⟨seq, hseq⟩ : ∃ seq : ℕ → C(X, ℂ), Filter.Tendsto seq Filter.atTop (nhds f) ∧ ∀ n, seq n ∈ Submodule.span ℂ (Set.range charMk) := by
      have h_dense : Dense (Submodule.span ℂ (Set.range charMk) : Set C(X, ℂ)) := by
        have h_star_subalgebra : ∃ A : StarSubalgebra ℂ C(X, ℂ), (A : Set C(X, ℂ)) = Submodule.span ℂ (Set.range charMk) := by
          refine' ⟨ _, _ ⟩;
          refine' { .. };
          exact ( Submodule.span ℂ ( Set.range charMk ) : Submodule ℂ C(X, ℂ) ) |> Submodule.toAddSubmonoid |> AddSubmonoid.toAddSubsemigroup |> AddSubsemigroup.carrier;
          all_goals norm_num;
          · intro a b ha hb;
            rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at ha hb;
            obtain ⟨ c, rfl ⟩ := ha; obtain ⟨ d, rfl ⟩ := hb; simp +decide [ Finsupp.sum, Finset.sum_mul _ _ _ ] ;
            simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, Finset.sum_mul, Submodule.mem_span ];
            intro p hp; refine' Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ _; refine' Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ _;
            have hmul : charMk i * charMk j = charMk (i + j) := by
              ext x; simp +decide [ charMk, charFun_add_apply ]
            rw [hmul]; exact hp ⟨ i + j, rfl ⟩
          · exact Submodule.subset_span ⟨ 0, by ext; simp +decide [ charMk, charFun_zero_apply ] ⟩;
          · exact fun ha hb => Submodule.add_mem _ ha hb;
          · intro r;
            rw [ Submodule.mem_span ];
            intro p hp;
            convert p.smul_mem r ( hp ⟨ 0, rfl ⟩ ) using 1;
            ext; simp [charMk];
            unfold charFun; aesop;
          · intro a ha;
            rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at ha;
            obtain ⟨ c, rfl ⟩ := ha;
            simp +decide [ Finsupp.sum, Submodule.mem_span ];
            intro p hp; exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ <| hp <| Set.mem_range.mpr ⟨ -i, by
              ext x; simp +decide [ charMk, charFun_neg_apply ] ; ⟩ ;
        obtain ⟨A, hA⟩ := h_star_subalgebra
        have h_separates_points : A.SeparatesPoints := by
          have h_separates_points : ∀ x y : X, x ≠ y → ∃ k : ℕ →₀ ℤ, charFun k x ≠ charFun k y := by
            intro x y hxy;
            have := charFun_separatesPoints hxy;
            aesop;
          intro x y hxy; obtain ⟨ k, hk ⟩ := h_separates_points x y hxy; use charMk k; simp_all +decide [ Set.ext_iff ] ;
          exact ⟨ Submodule.subset_span ⟨ k, rfl ⟩, hk ⟩;
        have := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A h_separates_points;
        simp_all +decide [ SetLike.ext_iff ];
        convert this using 1;
        rw [ show ( Submodule.span ℂ ( Set.range charMk ) : Set C(X, ℂ) ) = A from hA.symm ] ; simp +decide [ Dense ];
        rfl;
      have := h_dense f;
      rw [ mem_closure_iff_seq_limit ] at this ; tauto;
    refine' ⟨ fun n => ContinuousMap.toLp 2 haarProb ℂ ( seq n ), _, _ ⟩;
    · exact ContinuousMap.toLp 2 haarProb ℂ |>.continuous.continuousAt.tendsto.comp hseq.1;
    · intro n
      have h_seq_n : seq n ∈ Submodule.span ℂ (Set.range charMk) := hseq.right n
      have h_seq_n_Lp : ContinuousMap.toLp 2 haarProb ℂ (seq n) ∈ Submodule.span ℂ (Set.range charLp) := by
        rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at h_seq_n;
        obtain ⟨ c, hc ⟩ := h_seq_n; rw [ ← hc ] ; simp +decide [ Finsupp.sum, ContinuousMap.toLp ] ;
        exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ <| Submodule.subset_span <| Set.mem_range_self _
      exact h_seq_n_Lp;
  refine' eq_top_iff.mpr fun x hx => _;
  -- By the density of continuous functions in $L^2(X)$, there exists a sequence of continuous functions $f_n$ such that $f_n \to x$ in $L^2$.
  obtain ⟨f_n, hf_n⟩ : ∃ f_n : ℕ → C(X, ℂ), Filter.Tendsto (fun n => ContinuousMap.toLp 2 haarProb ℂ (f_n n)) Filter.atTop (nhds x) := by
    have := ContinuousMap.toLp_denseRange ( E := ℂ ) haarProb ( p := 2 ) ℂ ( by norm_num );
    have := this x;
    rw [ mem_closure_iff_seq_limit ] at this;
    exact ⟨ fun n => Classical.choose ( this.choose_spec.1 n ), by simpa only [ Classical.choose_spec ( this.choose_spec.1 _ ) ] using this.choose_spec.2 ⟩;
  choose seq hseq₁ hseq₂ using fun n => h_span_dense ( f_n n );
  -- By the properties of the limit, we can find a sequence in the span of the characters that converges to $x$.
  have h_seq : ∃ seq : ℕ → Lp ℂ 2 haarProb, Filter.Tendsto seq Filter.atTop (nhds x) ∧ ∀ n, seq n ∈ Submodule.span ℂ (Set.range charLp) := by
    have h_seq : ∀ n, ∃ m, dist (seq n m) (ContinuousMap.toLp 2 haarProb ℂ (f_n n)) < 1 / (n + 1) := by
      exact fun n => by rcases Metric.tendsto_atTop.mp ( hseq₁ n ) ( 1 / ( n + 1 ) ) ( by positivity ) with ⟨ m, hm ⟩ ; exact ⟨ m, hm m le_rfl ⟩ ;
    choose m hm using h_seq;
    use fun n => seq n (m n);
    exact ⟨ by simpa using Filter.Tendsto.add ( hf_n ) ( show Filter.Tendsto ( fun n => seq n ( m n ) - ( ContinuousMap.toLp 2 haarProb ℂ ) ( f_n n ) ) Filter.atTop ( nhds 0 ) from tendsto_zero_iff_norm_tendsto_zero.mpr <| squeeze_zero ( fun _ => by positivity ) ( fun n => le_of_lt <| by rw [ ← dist_eq_norm ]; simpa using hm n ) <| tendsto_one_div_add_atTop_nhds_zero_nat ), fun n => hseq₂ _ _ ⟩;
  exact mem_closure_of_tendsto h_seq.choose_spec.1 ( Filter.Eventually.of_forall h_seq.choose_spec.2 )

/-- **`h_dense`**: the union of the finite-window spans is dense in `L²(X, haarProb)`.
This is the Peter–Weyl theorem for the compact abelian group `X`: its characters span a
dense subspace of `L²`. It follows structurally from `iSup_H_eq` and `charSpan_dense`. -/
theorem H_dense : (⨆ n, H n).topologicalClosure = ⊤ := by
  rw [iSup_H_eq]; exact charSpan_dense

/-- Density in the `ε`-approximation form used by `projection_strong_convergence`:
for every `g ∈ L²(X)` and `ε > 0` there is a window `n` and an element of `H n`
within `ε` of `g`. Follows from `H_dense`. -/
theorem H_dense_approx (g : Lp ℂ 2 haarProb) (ε : ℝ) (hε : 0 < ε) :
    ∃ n, ∃ h : H n, ‖(h : Lp ℂ 2 haarProb) - g‖ < ε := by
  have h_dense : g ∈ (⨆ n, H n).topologicalClosure := by
    exact H_dense.symm ▸ Submodule.mem_top;
  have h_dense : ∀ ε > 0, ∃ y ∈ (⨆ n, H n), ‖y - g‖ < ε := by
    intro ε hε;
    simpa [ dist_eq_norm' ] using Metric.mem_closure_iff.mp h_dense ε hε;
  obtain ⟨ y, hy₁, hy₂ ⟩ := h_dense ε hε;
  rw [ Submodule.mem_iSup_of_directed ] at hy₁;
  · exact ⟨ hy₁.choose, ⟨ y, hy₁.choose_spec ⟩, hy₂ ⟩;
  · exact Monotone.directed_le H_mono

end KrafftSieve