import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.chi4_primeRecips_sub_const_powLog

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.DirichletCharacter

open scoped BigOperators

/-- `(chi4Fun a).re` is the `ℤ`-valued `χ₄` cast to `ℝ`. -/
private lemma chi4Fun_re_eq (a : ZMod 4) :
    (chi4Fun a).re = ((ZMod.χ₄ a : ℤ) : ℝ) := by
  rw [chi4Fun_eq_zmod]
  simp

/-- `|χ₄(n)| ≤ 1` for all `n : ℕ`. -/
private lemma chi4_abs_le_one (n : ℕ) :
    |((ZMod.χ₄ ((n : ℕ) : ZMod 4) : ℤ) : ℝ)| ≤ 1 := by
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  split_ifs <;> norm_num

/-- For `y ≥ 1`, `(log y)^10 ≤ 10^10 · y`. -/
private lemma log_pow_ten_le (y : ℝ) (hy : 1 ≤ y) :
    (Real.log y) ^ 10 ≤ (10 : ℝ) ^ 10 * y := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
  have h1 : Real.log y ≤ 10 * y ^ (1 / 10 : ℝ) := by
    have h := Real.log_le_rpow_div (le_of_lt hypos) (show (0 : ℝ) < 1 / 10 by norm_num)
    rw [div_eq_mul_inv, show (1 / 10 : ℝ)⁻¹ = 10 by norm_num] at h
    linarith [h, mul_comm (y ^ (1 / 10 : ℝ)) (10 : ℝ)]
  have h2 : (Real.log y) ^ 10 ≤ (10 * y ^ (1 / 10 : ℝ)) ^ 10 :=
    pow_le_pow_left₀ hlog h1 10
  have h3 : (10 * y ^ (1 / 10 : ℝ)) ^ 10 = (10 : ℝ) ^ 10 * y := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast (y ^ (1 / 10 : ℝ)) 10,
      ← Real.rpow_mul (le_of_lt hypos) (1 / 10 : ℝ) ((10 : ℕ) : ℝ),
      show (1 / 10 : ℝ) * ((10 : ℕ) : ℝ) = 1 by norm_num]
    exact Real.rpow_one y
  linarith [h2, h3]

/-- For `y ≥ 2`, `1/y ≤ 10^10 · (log y)^(-10)`. -/
private lemma inv_le_pow_log_neg (y : ℝ) (hy : 2 ≤ y) :
    (1 : ℝ) / y ≤ (10 : ℝ) ^ 10 * (Real.log y) ^ (-10 : ℝ) := by
  have hypos : 0 < y := by linarith
  have hlogpos : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog10pos : 0 < (Real.log y) ^ 10 := pow_pos hlogpos 10
  have hpow : (Real.log y) ^ 10 ≤ (10 : ℝ) ^ 10 * y := log_pow_ten_le y (by linarith)
  have hrec : 1 / ((10 : ℝ) ^ 10 * y) ≤ ((Real.log y) ^ 10)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hlog10pos hpow
  have hrpow : (Real.log y) ^ (-10 : ℝ) = ((Real.log y) ^ 10)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hlogpos) (10 : ℝ)]
    exact congrArg Inv.inv (Real.rpow_natCast (Real.log y) 10)
  rw [hrpow]
  have hkey : (1 : ℝ) / y = (10 : ℝ) ^ 10 * (1 / ((10 : ℝ) ^ 10 * y)) := by
    field_simp
  rw [hkey]
  exact mul_le_mul_of_nonneg_left hrec (by positivity)

theorem chi4_prime_recip_rate :
    ∃ L C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y →
      |(∑ p ∈ Nat.primesBelow y, ((ZMod.χ₄ ((p : ℕ) : ZMod 4) : ℤ) : ℝ) / (p : ℝ)) - L|
        ≤ C * (Real.log y) ^ (-10 : ℝ) := by
  obtain ⟨L, C₁, hC₁pos, hC₁⟩ := chi4_primeRecips_sub_const_powLog 10 (by norm_num)
  refine ⟨L, C₁ + 10 ^ 10, by positivity, ?_⟩
  intro y hy
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hypos : (0 : ℝ) < (y : ℝ) := by linarith
  have hlogpos : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
  set S : ℝ := ∑ p ∈ Nat.primesLE y, ((ZMod.χ₄ ((p : ℕ) : ZMod 4) : ℤ) : ℝ) / (p : ℝ)
    with hSdef
  set c : ℝ := (if y.Prime then ((ZMod.χ₄ ((y : ℕ) : ZMod 4) : ℤ) : ℝ) / (y : ℝ) else 0)
    with hcdef
  -- The commons bound, rewritten for the `primesLE` sum with `ZMod.χ₄`.
  have hboundS : |S - L| ≤ C₁ / (Real.log (y : ℝ)) ^ (10 : ℝ) := by
    rw [hSdef]
    have hS' := hC₁ (y : ℝ) hy2
    rw [Nat.floor_natCast] at hS'
    have hsum : (∑ p ∈ Nat.primesLE y, (chi4Fun ((p : ℕ) : ZMod 4)).re / (p : ℝ))
        = ∑ p ∈ Nat.primesLE y, ((ZMod.χ₄ ((p : ℕ) : ZMod 4) : ℤ) : ℝ) / (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [chi4Fun_re_eq]
    rw [hsum] at hS'
    exact hS'
  -- Splitting off the possible prime `y`.
  have hS_eq : S = (∑ p ∈ Nat.primesBelow y, ((ZMod.χ₄ ((p : ℕ) : ZMod 4) : ℤ) : ℝ) / (p : ℝ)) + c := by
    have hple : Nat.primesLE y = if y.Prime then insert y (Nat.primesBelow y) else Nat.primesBelow y := by
      show Nat.primesBelow (y + 1) = _
      exact Nat.primesBelow_succ y
    rw [hSdef, hcdef, hple]
    split_ifs with hp
    · rw [Finset.sum_insert (Nat.notMem_primesBelow y)]
      ring
    · ring
  have hdiff : |(∑ p ∈ Nat.primesBelow y, ((ZMod.χ₄ ((p : ℕ) : ZMod 4) : ℤ) : ℝ) / (p : ℝ)) - L|
      ≤ |S - L| + |c| := by
    have hT : (∑ p ∈ Nat.primesBelow y, ((ZMod.χ₄ ((p : ℕ) : ZMod 4) : ℤ) : ℝ) / (p : ℝ)) = S - c := by
      linarith [hS_eq]
    rw [hT]
    rw [show (S - c) - L = (S - L) + (-c) by ring]
    simpa using abs_add_le (S - L) (-c)
  -- Bound the boundary term by `1/y`.
  have hc_le : |c| ≤ 1 / (y : ℝ) := by
    rw [hcdef]
    split_ifs with hp
    · rw [abs_div, abs_of_pos hypos]
      refine div_le_div_of_nonneg_right (chi4_abs_le_one y) (le_of_lt hypos)
    · simp only [abs_zero]
      positivity
  have hinv : (1 : ℝ) / (y : ℝ) ≤ (10 : ℝ) ^ 10 * (Real.log (y : ℝ)) ^ (-10 : ℝ) :=
    inv_le_pow_log_neg (y : ℝ) hy2
  have hdiv : C₁ / (Real.log (y : ℝ)) ^ (10 : ℝ) = C₁ * (Real.log (y : ℝ)) ^ (-10 : ℝ) := by
    rw [div_eq_mul_inv, Real.rpow_neg (le_of_lt hlogpos) (10 : ℝ)]
  have hSb : |S - L| ≤ C₁ * (Real.log (y : ℝ)) ^ (-10 : ℝ) := hdiv ▸ hboundS
  calc |(∑ p ∈ Nat.primesBelow y, ((ZMod.χ₄ ((p : ℕ) : ZMod 4) : ℤ) : ℝ) / (p : ℝ)) - L|
      ≤ |S - L| + |c| := hdiff
    _ ≤ C₁ * (Real.log (y : ℝ)) ^ (-10 : ℝ) + (10 : ℝ) ^ 10 * (Real.log (y : ℝ)) ^ (-10 : ℝ) :=
        add_le_add hSb (le_trans hc_le hinv)
    _ = (C₁ + 10 ^ 10) * (Real.log (y : ℝ)) ^ (-10 : ℝ) := by ring

end Commons.NumberTheory.DirichletCharacter
