/-
Copyright (c) 2026 Fernando Portela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Portela
-/

import Mathlib.Tactic

/-
Definitions of Twin Prime Index and Krafft Solvability.
-/
def IsTwinPrimeIndex (m : ℕ) : Prop :=
  Nat.Prime (6 * m - 1) ∧ Nat.Prime (6 * m + 1)

def KrafftOperator (a b : ℤ) (e1 e2 : ℤ) : ℤ :=
  6 * a * b + e1 * a + e2 * b

def KrafftSolvable (m : ℕ) : Prop :=
  ∃ (a b : ℕ), a ≥ 1 ∧ b ≥ 1 ∧
  ∃ (e1 e2 : ℤ), (e1 = 1 ∨ e1 = -1) ∧ (e2 = 1 ∨ e2 = -1) ∧
  (m : ℤ) = KrafftOperator a b e1 e2

/-
If m is Krafft solvable, then it is not a twin prime index.
-/
theorem krafft_solvable_imp_not_twin_prime (m : ℕ) (hm : m ≥ 1) :
  KrafftSolvable m → ¬ IsTwinPrimeIndex m := by
    rintro ⟨ a, b, ha, hb, e1, e2, he1, he2, h ⟩ ⟨ h1, h2 ⟩
    -- Then $6m + e1 * e2 = (6a + e2)(6b + e1)$.
    have h_factor : (6 * m + e1 * e2 :) = (6 * a + e2) * (6 * b + e1) := by
      unfold KrafftOperator at h; linarith;
    -- Since $a, b \geq 1$, the factors $(6a + e2)$ and $(6b + e1)$ are both greater than $1$,
    -- so $6m + e1 * e2$ is composite.
    have h_composite : ¬Nat.Prime (Int.natAbs (6 * m + e1 * e2)) := by
      rw [ h_factor, Int.natAbs_mul ];
      exact Nat.not_prime_mul ( by cases he2 <;> cases he1 <;> omega )
                              ( by cases he2 <;> cases he1 <;> omega )
    rcases he1 with ( rfl | rfl ) <;> rcases he2 with ( rfl | rfl ) <;> norm_num at *
    · exact h_composite ( by norm_cast )
    · exact h_composite ( by convert h1 using 1; omega )
    · exact h_composite ( by convert h1 using 1; omega )
    · exact h_composite ( by simpa [ ← Int.natCast_dvd_natCast ] using h2 )

/-
Any integer x > 1 coprime to 6 can be written as 6a + e where a >= 1 and e is 1 or -1.
-/
lemma factor_form_6a_pm_1 (x : ℕ) (hx : x > 1) (h_cop : x.Coprime 6) :
  ∃ a : ℕ, a ≥ 1 ∧ ∃ e : ℤ, e ∈ ({-1, 1} : Set ℤ) ∧ (x : ℤ) = 6 * a + e := by
    -- Since $x$ is coprime to $6$, $x \% 6$ is $1$ or $5$.
    have h_mod : x % 6 = 1 ∨ x % 6 = 5 := by
      rw [ Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec ] at h_cop
      have := Nat.mod_lt x ( by decide : 6 > 0 )
      interval_cases x % 6 <;> trivial
    rcases h_mod <;> [ refine ⟨ x / 6, ?_, 1, ?_, ?_ ⟩ ;
                       refine ⟨ x / 6 + 1, ?_, -1, ?_, ?_ ⟩ ] <;> norm_num <;> omega;

/-
If 6m-1 factors as (6a+e1)(6b+e2), then m is Krafft solvable.
-/
lemma krafft_solvable_of_factorization_minus (m : ℕ) (a b : ℕ) (e1 e2 : ℤ)
  (ha : a ≥ 1) (hb : b ≥ 1)
  (he1 : e1 ∈ ({-1, 1} : Set ℤ)) (he2 : e2 ∈ ({-1, 1} : Set ℤ))
  (h_eq : (6 * m - 1 : ℤ) = (6 * a + e1) * (6 * b + e2)) :
  KrafftSolvable m := by
    use a, b;
    simp only [ge_iff_le, Int.reduceNeg, exists_and_left, exists_eq_or_imp, ↓existsAndEq, true_and]
    rcases he1 with ( rfl | rfl ) <;> rcases he2 with ( rfl | rfl ) <;> unfold KrafftOperator <;>
      ring_nf at *
    · omega
    · grind
    · grind
    · grind

/-
If 6m+1 factors as (6a+e1)(6b+e2), then m is Krafft solvable.
-/
lemma krafft_solvable_of_factorization_plus (m : ℕ) (a b : ℕ) (e1 e2 : ℤ)
  (ha : a ≥ 1) (hb : b ≥ 1)
  (he1 : e1 ∈ ({-1, 1} : Set ℤ)) (he2 : e2 ∈ ({-1, 1} : Set ℤ))
  (h_eq : (6 * m + 1 : ℤ) = (6 * a + e1) * (6 * b + e2)) :
  KrafftSolvable m := by
    rcases he1 with ( rfl | rfl ) <;> rcases he2 with ( rfl | rfl ) <;> (
      have := congr_arg ( · % 6 ) h_eq ; norm_num [ Int.add_emod, Int.mul_emod ] at this );
    · use a, b;
      exact ⟨ ha, hb, -1, -1, by decide, by decide, by
        unfold KrafftOperator
        linarith [ Nat.sub_add_cancel ( show a ≤ 6 * a * b from by nlinarith only [ ha, hb ] ),
                   Nat.sub_add_cancel ( show b ≤ 6 * a * b - a from by
                     exact le_tsub_of_add_le_left <| by nlinarith only [ ha, hb ] ) ] ⟩;
    · -- By definition of Krafft solvability, we need to find
      -- $a, b \geq 1$ and $e1, e2 \in \{-1, 1\}$ such that $m = 6ab + e2a + e1b$.
      use b, a, by linarith, by linarith, 1, 1;
      exact ⟨ Or.inl rfl, Or.inl rfl, by unfold KrafftOperator; linarith ⟩

/-
If m is not a twin prime index, then m is Krafft solvable.
-/
theorem not_twin_prime_imp_krafft_solvable (m : ℕ) (hm : m ≥ 1) :
  ¬ IsTwinPrimeIndex m → KrafftSolvable m := by
    -- Assume m is not a twin prime index. Then either 6m-1 or 6m+1 is composite.
    intro h_not_twin_prime
    by_cases h6m1 : Nat.Prime (6 * m - 1);
    · -- Since $6m+1$ is composite, there exist integers $a$ and $b$ such that
      -- $6m+1 = (6a+e1)(6 b+e2)$ with $a, b \geq 1$ and $e1, e2 \in \{-1, 1\}$.
      obtain ⟨a, b, ha, hb, he1, he2, h_eq⟩ : ∃ a b : ℕ, a ≥ 1 ∧ b ≥ 1 ∧ ∃ e1 e2 : ℤ,
        (e1 = 1 ∨ e1 = -1) ∧ (e2 = 1 ∨ e2 = -1) ∧
        (6 * m + 1 : ℤ) = (6 * a + e1) * (6 * b + e2) := by
        obtain ⟨p, hp⟩ : ∃ p : ℕ, 1 < p ∧ p < 6 * m + 1 ∧ p ∣ 6 * m + 1 := by
          exact Exists.imp ( by tauto ) ( Nat.exists_dvd_of_not_prime2 ( by linarith )
            ( show ¬ Nat.Prime ( 6 * m + 1 ) from fun h => h_not_twin_prime ⟨ h6m1, h ⟩ ) );
        -- Since $p$ is a factor of $6m+1$, we can write $p = 6a + e1$ for some
        -- $a \geq 1$ and $e 1 \in \{-1, 1\}$.
        obtain ⟨a, e1, ha, he1⟩ : ∃ a : ℕ, a ≥ 1 ∧
          ∃ e1 : ℤ, e1 ∈ ({-1, 1} : Set ℤ) ∧ (p : ℤ) = 6 * a + e1 := by
          have h_coprime : Nat.Coprime p 6 := by
            apply Nat.Coprime.coprime_dvd_left hp.2.2
            norm_num [ show 6 * m + 1 = 6 * m + 1 from rfl ]
          have := factor_form_6a_pm_1 p hp.1 h_coprime; aesop;
        -- Since $k$ is a factor of $6m+1$, we can write $k = 6b + e2$ for some
        -- $b \geq 1$ and $e2 \in  \{-1, 1\}$.
        obtain ⟨b, e2, hb, he2⟩ : ∃ b : ℕ, b ≥ 1 ∧ ∃ e2 : ℤ, e2 ∈ ({-1, 1} : Set ℤ) ∧
          (6 * m + 1) / p = 6 * b + e2 := by
          have hk : (6 * m + 1) / p > 1 := by
            nlinarith [ Nat.div_mul_cancel hp.2.2 ];
          have hk_coprime : Nat.Coprime ((6 * m + 1) / p) 6 := by
            apply Nat.Coprime.coprime_dvd_left ( Nat.div_dvd_of_dvd hp.2.2 )
            norm_num [ show 6 * m + 1 = 6 * m + 1 from rfl ]
          have := factor_form_6a_pm_1 ( ( 6 * m + 1 ) / p ) hk hk_coprime; aesop;
        use a, b, e1, e2, ha, hb;
        exact ⟨ by simpa [ or_comm ] using he1.1, by simpa [ or_comm ] using he2.1,
          by rw [ ← he1.2, ← he2.2, Int.mul_ediv_cancel' ( mod_cast hp.2.2 ) ] ⟩;
      exact krafft_solvable_of_factorization_plus m a b he1 he2 ha hb
        ( by aesop ) ( by aesop ) h_eq.2.2;
    · -- Since $6m-1$ is composite, there exist integers $p$ and $q$ such that $1 < p < 6m-1$
      -- and $1 < q < 6m-1$, and $pq = 6m-1$.
      obtain ⟨p, q, hp, hq, hpq⟩ : ∃ p q : ℕ, 1 < p ∧ 1 < q ∧ p * q = 6 * m - 1 := by
        rcases Nat.exists_dvd_of_not_prime2 ( Nat.le_sub_one_of_lt ( by linarith ) )
          h6m1 with ⟨ p, hp₁, hp₂ ⟩ ; exact ⟨ p, ( 6 * m - 1 ) / p,
            by nlinarith [ Nat.div_mul_cancel hp₁ ],
            by nlinarith [ Nat.div_mul_cancel hp₁ ],
            by rw [ mul_comm, Nat.div_mul_cancel hp₁ ] ⟩;
      -- By `factor_form_6a_pm_1`, $p = 6a + e_1$ and $q = 6b + e_2$ for some $a, b \geq 1$
      -- and $e_1, e_2 \in \{-1, 1\}$.
      obtain ⟨a, ha, e1, he1, hp_eq⟩ : ∃ a : ℕ, a ≥ 1 ∧ ∃ e1 : ℤ, e1 ∈ ({-1, 1} : Set ℤ) ∧
        (p : ℤ) = 6 * a + e1 := by
        apply factor_form_6a_pm_1 p hp
        apply Nat.Coprime.coprime_dvd_left (Dvd.intro q hpq)
        cases m <;> simp_all +decide [ Nat.mul_succ ]
      obtain ⟨b, hb, e2, he2, hq_eq⟩ : ∃ b : ℕ, b ≥ 1 ∧ ∃ e2 : ℤ, e2 ∈ ({-1, 1} : Set ℤ) ∧
        (q : ℤ) = 6 * b + e2 := by
        apply factor_form_6a_pm_1 q hq
        apply Nat.Coprime.coprime_dvd_left (show q ∣ p * q from ⟨p, by rw [Nat.mul_comm]⟩)
        rw [hpq]
        cases m <;> norm_num [Nat.succ_eq_add_one, Nat.mul_succ] at *
      apply krafft_solvable_of_factorization_minus m a b e1 e2 ha hb he1 he2;
      nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ 6 * m ) ]

/-
Proposition 1: The pair {6m-1, 6m+1} consists of twin primes if and only if the Diophantine
equation m = 6ab + e1 a + e2 b has no solutions.
-/
theorem krafft_bi_implication (m : ℕ) (hm : m ≥ 1) :
  IsTwinPrimeIndex m ↔ ¬ KrafftSolvable m := by
    exact ⟨ fun h => fun h' => krafft_solvable_imp_not_twin_prime m hm h' h, fun h => by
      have := not_twin_prime_imp_krafft_solvable m hm; tauto ⟩
