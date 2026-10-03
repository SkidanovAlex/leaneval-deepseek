import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.card_Omega_eq_le
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_two_pow_omega_div_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

open scoped BigOperators
open Finset

noncomputable section

/-! ## Bounding the genuine local factors

For a prime `p` and `χ = χ₄(p) ∈ {0, ±1}` we have

* `f₁(p) = ((1+χ)(p-1)+1)/p² ≤ 2/p`,
* `f₂(p) = ((1+χ)(p-1)+p)/p³ ≤ 3/p²`,

and both are nonnegative. -/

private lemma chi4_real_le_one (a : ZMod 4) : (ZMod.χ₄ a : ℝ) ≤ 1 := by
  have h : (ZMod.χ₄ a : ℤ) ≤ 1 := by fin_cases a <;> decide
  exact_mod_cast h

private lemma chi4_real_ge_neg_one (a : ZMod 4) : (-1 : ℝ) ≤ (ZMod.χ₄ a : ℝ) := by
  have h : (-1 : ℤ) ≤ ZMod.χ₄ a := by fin_cases a <;> decide
  exact_mod_cast h

private lemma one_add_chi4_nonneg (p : ℕ) : 0 ≤ (1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ) := by
  have h := chi4_real_ge_neg_one (p : ZMod 4)
  linarith

private lemma one_add_chi4_le_two (p : ℕ) : (1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ) ≤ 2 := by
  have h := chi4_real_le_one (p : ZMod 4)
  linarith

private lemma f1_nonneg {p : ℕ} (hp : 1 ≤ p) :
    0 ≤ (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + 1) / (p : ℝ) ^ 2 := by
  have h1 : 0 ≤ (1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ) := one_add_chi4_nonneg p
  have h2 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have h3 : 0 ≤ ((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) := mul_nonneg h1 h2
  exact div_nonneg (by linarith) (by positivity)

private lemma f1_le_two_div {p : ℕ} (hp : 1 ≤ p) :
    (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + 1) / (p : ℝ) ^ 2
      ≤ 2 / (p : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have h1 : (1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ) ≤ 2 := one_add_chi4_le_two p
  have h2 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have h3 := mul_le_mul_of_nonneg_right h1 h2
  have hnum : ((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + 1 ≤ 2 * (p : ℝ) := by
    nlinarith [h3]
  calc (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + 1) / (p : ℝ) ^ 2
      ≤ (2 * (p : ℝ)) / (p : ℝ) ^ 2 := div_le_div_of_nonneg_right hnum (by positivity)
    _ = 2 / (p : ℝ) := by field_simp

private lemma f2_nonneg {p : ℕ} (hp : 1 ≤ p) :
    0 ≤ (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + (p : ℝ)) / (p : ℝ) ^ 3 := by
  have h1 : 0 ≤ (1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ) := one_add_chi4_nonneg p
  have h2 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hpnn : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have h3 : 0 ≤ ((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) := mul_nonneg h1 h2
  exact div_nonneg (by linarith) (by positivity)

private lemma f2_le_three_div_sq {p : ℕ} (hp : 1 ≤ p) :
    (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + (p : ℝ)) / (p : ℝ) ^ 3
      ≤ 3 / (p : ℝ) ^ 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have h1 : (1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ) ≤ 2 := one_add_chi4_le_two p
  have h2 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have h3 := mul_le_mul_of_nonneg_right h1 h2
  have hnum : ((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + (p : ℝ)
      ≤ 3 * (p : ℝ) := by
    nlinarith [h3]
  calc (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + (p : ℝ)) / (p : ℝ) ^ 3
      ≤ (3 * (p : ℝ)) / (p : ℝ) ^ 3 := div_le_div_of_nonneg_right hnum (by positivity)
    _ = 3 / (p : ℝ) ^ 2 := by field_simp

/-! ## Product bounds over the prime factors -/

private lemma prod_two_div_eq (d : ℕ) (hsq : Squarefree d) :
    (∏ p ∈ d.primeFactors, (2 : ℝ) / (p : ℝ)) = (2 : ℝ) ^ (d.primeFactors).card / (d : ℝ) := by
  rw [Finset.prod_div_distrib, Finset.prod_const]
  congr 1
  rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]

private lemma prod_one_div_eq (d : ℕ) (hsq : Squarefree d) :
    (∏ p ∈ d.primeFactors, (1 : ℝ) / (p : ℝ)) = 1 / (d : ℝ) := by
  rw [Finset.prod_div_distrib, Finset.prod_const]
  simp only [one_pow]
  congr 1
  rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]

/-- For any finite set of primes, `∏_{p ∈ S} 3/p ≤ 3/2`. -/
private lemma prod_three_div_le (S : Finset ℕ) (h : ∀ p ∈ S, Nat.Prime p) :
    (∏ p ∈ S, (3 : ℝ) / (p : ℝ)) ≤ 3 / 2 := by
  classical
  have hthree : ∀ p ∈ S, p ≠ 2 → 3 ≤ p := by
    intro p hp hp2
    have := (h p hp).two_le
    omega
  by_cases h2 : 2 ∈ S
  · have hsplit : (∏ p ∈ S, (3 : ℝ) / (p : ℝ))
        = (3 : ℝ) / 2 * ∏ p ∈ S.erase 2, (3 : ℝ) / (p : ℝ) := by
      conv_lhs => rw [← Finset.insert_erase h2]
      rw [Finset.prod_insert (Finset.notMem_erase 2 S)]
      norm_num
    rw [hsplit]
    have hle1 : (∏ p ∈ S.erase 2, (3 : ℝ) / (p : ℝ)) ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro p hp
        have hp3 : 3 ≤ p := hthree p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp)
        exact div_nonneg (by norm_num) (by positivity)
      · intro p hp
        have hp3 : 3 ≤ p := hthree p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp)
        rw [div_le_one (by positivity)]
        exact_mod_cast hp3
    calc (3 : ℝ) / 2 * (∏ p ∈ S.erase 2, (3 : ℝ) / (p : ℝ))
        ≤ (3 : ℝ) / 2 * 1 := mul_le_mul_of_nonneg_left hle1 (by norm_num)
      _ = 3 / 2 := by norm_num
  · have hle1 : (∏ p ∈ S, (3 : ℝ) / (p : ℝ)) ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro p hp
        exact div_nonneg (by norm_num) (by positivity)
      · intro p hp
        have hne : p ≠ 2 := fun hh => h2 (hh ▸ hp)
        have hp3 : 3 ≤ p := hthree p hp hne
        rw [div_le_one (by positivity)]
        exact_mod_cast hp3
    linarith

/-- The product of the genuine `d₁`-factors is at most `2^ω(d₁)/d₁`. -/
private lemma gdens_prod1_le (d : ℕ) (hsq : Squarefree d) :
    (∏ p ∈ d.primeFactors,
        (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + 1) / (p : ℝ) ^ 2)
      ≤ (2 : ℝ) ^ (d.primeFactors).card / (d : ℝ) := by
  calc (∏ p ∈ d.primeFactors,
        (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + 1) / (p : ℝ) ^ 2)
      ≤ ∏ p ∈ d.primeFactors, (2 : ℝ) / (p : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          exact f1_nonneg (Nat.prime_of_mem_primeFactors hp).one_le
        · intro p hp
          exact f1_le_two_div (Nat.prime_of_mem_primeFactors hp).one_le
    _ = (2 : ℝ) ^ (d.primeFactors).card / (d : ℝ) := prod_two_div_eq d hsq

/-- The product of the genuine `d₂`-factors is at most `(3/2)/d₂`. -/
private lemma gdens_prod2_le (d : ℕ) (hsq : Squarefree d) :
    (∏ p ∈ d.primeFactors,
        (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + (p : ℝ)) / (p : ℝ) ^ 3)
      ≤ (3 / 2) / (d : ℝ) := by
  have h1 : (∏ p ∈ d.primeFactors,
        (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + (p : ℝ)) / (p : ℝ) ^ 3)
      ≤ ∏ p ∈ d.primeFactors, (3 : ℝ) / (p : ℝ) ^ 2 := by
    apply Finset.prod_le_prod₀
    · intro p hp
      exact f2_nonneg (Nat.prime_of_mem_primeFactors hp).one_le
    · intro p hp
      exact f2_le_three_div_sq (Nat.prime_of_mem_primeFactors hp).one_le
  have h2 : (∏ p ∈ d.primeFactors, (3 : ℝ) / (p : ℝ) ^ 2)
      = (∏ p ∈ d.primeFactors, (3 : ℝ) / (p : ℝ))
        * (∏ p ∈ d.primeFactors, (1 : ℝ) / (p : ℝ)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by
      have := (Nat.prime_of_mem_primeFactors hp).ne_zero
      positivity
    field_simp
  have h3 : (∏ p ∈ d.primeFactors, (3 : ℝ) / (p : ℝ)) ≤ 3 / 2 :=
    prod_three_div_le d.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have h4 : (∏ p ∈ d.primeFactors, (1 : ℝ) / (p : ℝ)) = 1 / (d : ℝ) := prod_one_div_eq d hsq
  have h5 : (0 : ℝ) ≤ ∏ p ∈ d.primeFactors, (1 : ℝ) / (p : ℝ) := by
    apply Finset.prod_nonneg
    intro p hp
    exact div_nonneg (by norm_num) (by positivity)
  have h6 : (0 : ℝ) ≤ 3 / 2 := by norm_num
  calc (∏ p ∈ d.primeFactors,
        (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + (p : ℝ)) / (p : ℝ) ^ 3)
      ≤ ∏ p ∈ d.primeFactors, (3 : ℝ) / (p : ℝ) ^ 2 := h1
    _ = (∏ p ∈ d.primeFactors, (3 : ℝ) / (p : ℝ))
        * (∏ p ∈ d.primeFactors, (1 : ℝ) / (p : ℝ)) := h2
    _ ≤ (3 / 2) * (1 / (d : ℝ)) := by
        rw [h4]
        exact mul_le_mul h3 le_rfl (by positivity) h6
    _ = (3 / 2) / (d : ℝ) := by ring

end

/-- The local-density summatory bound for the Friedlander–Iwaniec density `g` on
cubefree moduli `d = d₁ d₂²`, with the **genuine** local factors
`g(p) = ((1+χ₄(p))(p−1) + 1)/p²` (for `p ∣ d₁`) and
`g(p²) = ((1+χ₄(p))(p−1) + p)/p³` (for `p ∣ d₂`), as in Lemma 3.4 / (3.16) of
Friedlander–Iwaniec, Ann. of Math. 148 (1998). -/
theorem sum_gdens_cubefree_prod_le_final :
    ∃ C A : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y →
      (∑ d₁ ∈ Finset.Icc 1 y, ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y),
        if Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧ ¬ 4 ∣ d₁ * d₂ ^ 2
          ∧ d₁ * d₂ ^ 2 ≤ y then
          (∏ p ∈ d₁.primeFactors,
              (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + 1) / (p : ℝ) ^ 2)
          * (∏ p ∈ d₂.primeFactors,
              (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + (p : ℝ)) / (p : ℝ) ^ 3)
        else 0)
        ≤ C * (Real.log y) ^ A := by
  refine ⟨(3 / 2) * (1 + 1 / Real.log 2) ^ (3 : ℕ), 3, ?_, ?_⟩
  · have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · intro y hy
    rw [Real.rpow_ofNat]
    have hterm : ∀ d₁ ∈ Finset.Icc 1 y, ∀ d₂ ∈ Finset.Icc 1 (Nat.sqrt y),
        (if Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧ ¬ 4 ∣ d₁ * d₂ ^ 2
            ∧ d₁ * d₂ ^ 2 ≤ y then
          (∏ p ∈ d₁.primeFactors,
              (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + 1) / (p : ℝ) ^ 2)
          * (∏ p ∈ d₂.primeFactors,
              (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + (p : ℝ)) / (p : ℝ) ^ 3)
        else 0)
        ≤ ((2 : ℝ) ^ (d₁.primeFactors).card / (d₁ : ℝ)) * ((3 / 2) / (d₂ : ℝ)) := by
      intro d₁ _ d₂ _
      by_cases hc : (Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧ ¬ 4 ∣ d₁ * d₂ ^ 2
            ∧ d₁ * d₂ ^ 2 ≤ y)
      · rw [if_pos hc]
        obtain ⟨hs1, hs2, -,-,-⟩ := hc
        have hP2nn : (0 : ℝ) ≤ ∏ p ∈ d₂.primeFactors,
            (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + (p : ℝ)) / (p : ℝ) ^ 3 :=
          Finset.prod_nonneg (fun p hp =>
            f2_nonneg (Nat.prime_of_mem_primeFactors hp).one_le)
        exact mul_le_mul (gdens_prod1_le d₁ hs1) (gdens_prod2_le d₂ hs2)
          hP2nn (by positivity)
      · rw [if_neg hc]
        positivity
    have hstep1 : (∑ d₁ ∈ Finset.Icc 1 y, ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y),
        (if Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧ ¬ 4 ∣ d₁ * d₂ ^ 2
            ∧ d₁ * d₂ ^ 2 ≤ y then
          (∏ p ∈ d₁.primeFactors,
              (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + 1) / (p : ℝ) ^ 2)
          * (∏ p ∈ d₂.primeFactors,
              (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + (p : ℝ)) / (p : ℝ) ^ 3)
        else 0))
        ≤ ∑ d₁ ∈ Finset.Icc 1 y, ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y),
            ((2 : ℝ) ^ (d₁.primeFactors).card / (d₁ : ℝ)) * ((3 / 2) / (d₂ : ℝ)) := by
      apply Finset.sum_le_sum; intro d₁ hd₁
      apply Finset.sum_le_sum; intro d₂ hd₂
      exact hterm d₁ hd₁ d₂ hd₂
    have hstep2 : (∑ d₁ ∈ Finset.Icc 1 y, ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y),
            ((2 : ℝ) ^ (d₁.primeFactors).card / (d₁ : ℝ)) * ((3 / 2) / (d₂ : ℝ)))
        = (∑ d₁ ∈ Finset.Icc 1 y, (2 : ℝ) ^ (d₁.primeFactors).card / (d₁ : ℝ))
          * (∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y), (3 / 2) / (d₂ : ℝ)) :=
      (Finset.sum_mul_sum _ _ _ _).symm
    have hb1 : (∑ d₁ ∈ Finset.Icc 1 y, (2 : ℝ) ^ (d₁.primeFactors).card / (d₁ : ℝ))
        ≤ (1 + Real.log (y : ℝ)) ^ 2 :=
      Commons.NumberTheory.ArithmeticFunction.sum_two_pow_omega_div_le y
    have hb2 : (∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y), (3 / 2) / (d₂ : ℝ))
        ≤ (3 / 2) * (1 + Real.log ((Nat.sqrt y : ℕ) : ℝ)) := by
      have hrew : (∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y), (3 / 2) / (d₂ : ℝ))
          = (3 / 2) * ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y), (1 : ℝ) / (d₂ : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
      rw [hrew]
      exact mul_le_mul_of_nonneg_left
        (Commons.NumberTheory.ArithmeticFunction.sum_inv_Icc_one_le_one_add_log (Nat.sqrt y))
        (by norm_num)
    have hnn2 : (0 : ℝ) ≤ ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y), (3 / 2) / (d₂ : ℝ) :=
      Finset.sum_nonneg (fun d _ => by positivity)
    have hbase_y : (0 : ℝ) ≤ (1 + Real.log (y : ℝ)) ^ 2 := by positivity
    have hcomb : (∑ d₁ ∈ Finset.Icc 1 y, (2 : ℝ) ^ (d₁.primeFactors).card / (d₁ : ℝ))
          * (∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y), (3 / 2) / (d₂ : ℝ))
        ≤ (1 + Real.log (y : ℝ)) ^ 2 * ((3 / 2) * (1 + Real.log ((Nat.sqrt y : ℕ) : ℝ))) :=
      mul_le_mul hb1 hb2 hnn2 hbase_y
    have hlogy_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogsqrt : Real.log ((Nat.sqrt y : ℕ) : ℝ) ≤ Real.log (y : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast (Nat.sqrt_pos.mpr (by omega : 0 < y))
      · exact_mod_cast Nat.sqrt_le_self y
    have h1 : 1 + Real.log ((Nat.sqrt y : ℕ) : ℝ) ≤ 1 + Real.log (y : ℝ) := by linarith
    have hge : Real.log 2 ≤ Real.log (y : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hy)
    have hstep : 1 + Real.log (y : ℝ) ≤ (1 + 1 / Real.log 2) * Real.log (y : ℝ) := by
      have hdiv : 1 ≤ Real.log (y : ℝ) / Real.log 2 := (one_le_div hlog2).mpr hge
      have hA : 1 ≤ (Real.log 2)⁻¹ * Real.log (y : ℝ) := by
        rw [inv_mul_eq_div]; exact hdiv
      have heq : (1 + 1 / Real.log 2) * Real.log (y : ℝ)
          = Real.log (y : ℝ) + (Real.log 2)⁻¹ * Real.log (y : ℝ) := by
        rw [one_div, add_mul, one_mul]
      rw [heq]; linarith
    have hbase : (0 : ℝ) ≤ 1 + Real.log (y : ℝ) := by linarith
    have hfinal : (1 + Real.log (y : ℝ)) ^ 2 * ((3 / 2) * (1 + Real.log ((Nat.sqrt y : ℕ) : ℝ)))
        ≤ ((3 / 2) * (1 + 1 / Real.log 2) ^ (3 : ℕ)) * (Real.log (y : ℝ)) ^ 3 := by
      have hA : (1 + Real.log (y : ℝ)) ^ 2 * (1 + Real.log ((Nat.sqrt y : ℕ) : ℝ))
          ≤ (1 + Real.log (y : ℝ)) ^ 3 := by
        calc (1 + Real.log (y : ℝ)) ^ 2 * (1 + Real.log ((Nat.sqrt y : ℕ) : ℝ))
            ≤ (1 + Real.log (y : ℝ)) ^ 2 * (1 + Real.log (y : ℝ)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = (1 + Real.log (y : ℝ)) ^ 3 := by ring
      have hB : (1 + Real.log (y : ℝ)) ^ 3
          ≤ ((1 + 1 / Real.log 2) * Real.log (y : ℝ)) ^ 3 := pow_le_pow_left₀ hbase hstep 3
      have hC : ((1 + 1 / Real.log 2) * Real.log (y : ℝ)) ^ 3
          = (1 + 1 / Real.log 2) ^ (3 : ℕ) * (Real.log (y : ℝ)) ^ 3 := by ring
      calc (1 + Real.log (y : ℝ)) ^ 2 * ((3 / 2) * (1 + Real.log ((Nat.sqrt y : ℕ) : ℝ)))
          = (3 / 2) * ((1 + Real.log (y : ℝ)) ^ 2 * (1 + Real.log ((Nat.sqrt y : ℕ) : ℝ))) := by
            ring
        _ ≤ (3 / 2) * (1 + Real.log (y : ℝ)) ^ 3 := by
            exact mul_le_mul_of_nonneg_left hA (by norm_num)
        _ ≤ (3 / 2) * ((1 + 1 / Real.log 2) * Real.log (y : ℝ)) ^ 3 := by
            exact mul_le_mul_of_nonneg_left hB (by norm_num)
        _ = ((3 / 2) * (1 + 1 / Real.log 2) ^ (3 : ℕ)) * (Real.log (y : ℝ)) ^ 3 := by
            rw [hC]; ring
    calc (∑ d₁ ∈ Finset.Icc 1 y, ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y),
        (if Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧ ¬ 4 ∣ d₁ * d₂ ^ 2
            ∧ d₁ * d₂ ^ 2 ≤ y then
          (∏ p ∈ d₁.primeFactors,
              (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + 1) / (p : ℝ) ^ 2)
          * (∏ p ∈ d₂.primeFactors,
              (((1 : ℝ) + ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ)) * ((p : ℝ) - 1) + (p : ℝ)) / (p : ℝ) ^ 3)
        else 0))
        ≤ (∑ d₁ ∈ Finset.Icc 1 y, ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y),
            ((2 : ℝ) ^ (d₁.primeFactors).card / (d₁ : ℝ)) * ((3 / 2) / (d₂ : ℝ))) := hstep1
      _ = (∑ d₁ ∈ Finset.Icc 1 y, (2 : ℝ) ^ (d₁.primeFactors).card / (d₁ : ℝ))
            * (∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y), (3 / 2) / (d₂ : ℝ)) := hstep2
      _ ≤ (1 + Real.log (y : ℝ)) ^ 2 * ((3 / 2) * (1 + Real.log ((Nat.sqrt y : ℕ) : ℝ))) := hcomb
      _ ≤ ((3 / 2) * (1 + 1 / Real.log 2) ^ (3 : ℕ)) * (Real.log (y : ℝ)) ^ 3 := hfinal

end Commons.NumberTheory.FriedlanderIwaniec
