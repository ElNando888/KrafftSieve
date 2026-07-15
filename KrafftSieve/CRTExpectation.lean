import Mathlib

namespace KrafftSieve

/-
In a complete CRT period, fixing one coordinate of a family of two independent
choices leaves exactly half of the Boolean choices.  This weighted form is the
combinatorial summation identity needed by the Gibbs-dip expectation argument.
-/
set_option maxHeartbeats 800000 in
lemma crt_two_choices_coordinate_sum {m : ℕ} (a : Fin m → ℕ)
    [NeZero (∏ i, a i)]
    (hcop : Pairwise (fun i j => Nat.Coprime (a i) (a j)))
    (u v : (i : Fin m) → ZMod (a i)) (hne : ∀ i, u i ≠ v i)
    (i : Fin m) (f : ZMod (a i) → ℝ) :
    ∑ y ∈ (Finset.Ico 0 ((∏ j, a j) : ℤ)).filter (fun y : ℤ =>
        ∀ j, (y : ZMod (a j)) = u j ∨ (y : ZMod (a j)) = v j),
      f (y : ZMod (a i)) =
      (2 ^ (m - 1) : ℝ) * (f (u i) + f (v i)) := by
  obtain ⟨g, hg⟩ : ∃ g : (∀ j, ZMod (a j)) ≃+* ZMod (∏ j, (a j)), ∀ j x, ((g x).val : ZMod (a j)) = x j := by
    -- By the Chinese Remainder Theorem, there exists a ring isomorphism between $ZMod (\prod_{j} a_j)$ and $\prod_{j} ZMod (a_j)$.
    have h_crt_iso : Nonempty (ZMod (∏ j, (a j)) ≃+* (∀ j, ZMod (a j))) := by
      exact ⟨ ( ZMod.prodEquivPi a hcop ) ⟩;
    obtain ⟨ g ⟩ := h_crt_iso;
    refine' ⟨ g.symm, _ ⟩;
    intro j x
    have h_crt_iso : ∀ y : ZMod (∏ j, (a j)), (g y) j = y.val := by
      intro y
      have h_crt_iso : ∀ y : ℕ, y < ∏ j, (a j) → (g y) j = y := by
        intro y hy; have := g.map_add ( y : ZMod ( ∏ j, a j ) ) 0; simp_all +decide [ ZMod.natCast_eq_zero_iff ] ;
      have := h_crt_iso y.val ( ZMod.val_lt y ) ; aesop;
    rw [ ← h_crt_iso, g.apply_symm_apply ];
  -- Consider the set of all possible combinations of $u$ and $v$.
  set S := Finset.image (fun b : (j : Fin m) → Bool => g (fun j => if b j then v j else u j)) (Finset.univ : Finset ((j : Fin m) → Bool)) with hS_def;
  -- By definition of $S$, we know that every element in $S$ is of the form $g(b)$ for some $b : (j : Fin m) → Bool$.
  have hS : Finset.filter (fun y : ℕ => ∀ j, (y : ZMod (a j)) = u j ∨ (y : ZMod (a j)) = v j) (Finset.Ico 0 (∏ j, (a j))) = Finset.image (fun x => x.val) S := by
    ext y; simp [hS_def];
    constructor;
    · intro hy
      obtain ⟨b, hb⟩ : ∃ b : (j : Fin m) → Bool, ∀ j, (y : ZMod (a j)) = if b j then v j else u j := by
        exact ⟨ fun j => if ( y : ZMod ( a j ) ) = v j then Bool.true else Bool.false, fun j => by specialize hy; specialize hy; cases hy.2 j <;> aesop ⟩;
      use b;
      convert congr_arg ZMod.val ( g.apply_symm_apply ( y : ZMod ( ∏ j, a j ) ) ) using 1;
      · congr! 2;
        ext j; specialize hg j ( g.symm ( y : ZMod ( ∏ j, a j ) ) ) ; aesop;
      · exact Eq.symm ( ZMod.val_cast_of_lt hy.1 );
    · rintro ⟨ b, rfl ⟩ ; exact ⟨ by exact ZMod.val_lt _, fun j => by specialize hg j ( fun j => if b j = true then v j else u j ) ; aesop ⟩ ;
  -- By definition of $S$, we know that every element in $S$ is of the form $g(b)$ for some $b : (j : Fin m) → Bool$. Therefore, we can rewrite the sum as:
  have h_sum : ∑ y ∈ Finset.filter (fun y : ℕ => ∀ j, (y : ZMod (a j)) = u j ∨ (y : ZMod (a j)) = v j) (Finset.Ico 0 (∏ j, (a j))), f (y : ZMod (a i)) = ∑ b : (j : Fin m) → Bool, f (if b i then v i else u i) := by
    rw [ show ( Finset.filter ( fun y : ℕ => ∀ j : Fin m, ( y : ZMod ( a j ) ) = u j ∨ ( y : ZMod ( a j ) ) = v j ) ( Finset.Ico 0 ( ∏ j : Fin m, a j ) ) ) = Finset.image ( fun b : ( j : Fin m ) → Bool => ( g fun j => if b j = true then v j else u j ).val ) Finset.univ from ?_ ];
    · rw [ Finset.sum_image ];
      · exact Finset.sum_congr rfl fun x hx => by specialize hg i ( fun j => if x j = true then v j else u j ) ; aesop;
      · intro b hb b' hb' h; have := hg i ( fun j => if b j then v j else u j ) ; have := hg i ( fun j => if b' j then v j else u j ) ; simp_all +decide [ funext_iff ] ;
        have := g.injective ( show g ( fun k => if b k then v k else u k ) = g ( fun k => if b' k then v k else u k ) from by
                                exact ZMod.val_injective _ h ) ; simp_all +decide [ funext_iff ] ;
        grind;
    · aesop;
  convert h_sum using 1;
  · refine' Finset.sum_bij ( fun x hx => Int.toNat x ) _ _ _ _ <;> simp +decide [ Int.toNat_of_nonneg ];
    · intro x hx₁ hx₂ hx₃; norm_cast at *; simp_all +decide [ Int.toNat_of_nonneg hx₁ ] ;
    · grind;
    · exact fun b hb hb' => ⟨ b, ⟨ ⟨ Nat.cast_nonneg _, mod_cast hb ⟩, mod_cast hb' ⟩, rfl ⟩;
    · exact fun x hx₁ hx₂ hx₃ => by rw [ ← Int.toNat_of_nonneg hx₁ ] ; norm_cast;
  · -- Let's simplify the sum $\sum_{b : (j : Fin m) → Bool} f (if b i then v i else u i)$.
    have h_sum_simplified : ∑ b : (j : Fin m) → Bool, f (if b i then v i else u i) = ∑ b : (j : Fin m) → Bool, f (u i) + ∑ b : (j : Fin m) → Bool, (f (v i) - f (u i)) * (if b i then 1 else 0) := by
      rw [ ← Finset.sum_add_distrib ] ; congr ; ext b ; split_ifs <;> ring;
    -- Let's simplify the sum $\sum_{b : (j : Fin m) → Bool} (f (v i) - f (u i)) * (if b i then 1 else 0)$.
    have h_sum_indicator : ∑ b : (j : Fin m) → Bool, (if b i then 1 else 0) = 2 ^ (m - 1) := by
      have h_sum_indicator : Finset.card (Finset.filter (fun b : (j : Fin m) → Bool => b i = true) Finset.univ) = Finset.card (Finset.univ : Finset ((j : Fin m) → Bool)) / 2 := by
        have h_sum_indicator : Finset.card (Finset.filter (fun b : (j : Fin m) → Bool => b i = true) Finset.univ) = Finset.card (Finset.filter (fun b : (j : Fin m) → Bool => b i = false) Finset.univ) := by
          rw [ Finset.card_filter, Finset.card_filter ];
          rw [ ← Equiv.sum_comp ( Equiv.addRight ( Pi.single i true ) ) ] ; aesop;
        have h_sum_indicator : Finset.card (Finset.filter (fun b : (j : Fin m) → Bool => b i = true) Finset.univ) + Finset.card (Finset.filter (fun b : (j : Fin m) → Bool => b i = false) Finset.univ) = Finset.card (Finset.univ : Finset ((j : Fin m) → Bool)) := by
          rw [ Finset.card_filter, Finset.card_filter ];
          rw [ ← Finset.sum_add_distrib, Finset.card_eq_sum_ones ] ; congr ; ext ; aesop;
        grind;
      cases m <;> simp_all +decide [ pow_succ' ];
      exact Fin.elim0 i;
    simp_all +decide [ Finset.sum_ite ];
    cases m <;> simp_all +decide [ pow_succ' ] ; ring;
    · fin_cases i;
    · ring

end KrafftSieve