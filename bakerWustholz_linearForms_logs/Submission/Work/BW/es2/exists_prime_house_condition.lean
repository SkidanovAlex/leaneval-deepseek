import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.es2

/-- For every real `t`, `(1 - t) * exp t ≤ 1`.  This is the standard bound
`exp t ≤ 1/(1-t)` for `t < 1`, obtained from `exp (-t) ≥ 1 - t`. -/
lemma one_sub_mul_exp_le_one (t : ℝ) : (1 - t) * Real.exp t ≤ 1 := by
  have h := Real.add_one_le_exp (-t)
  rw [Real.exp_neg] at h
  have h' : 1 - t ≤ (Real.exp t)⁻¹ := by linarith
  rw [inv_eq_one_div] at h'
  exact (le_div_iff₀ (Real.exp_pos t)).mp h'

/-- A concrete numeric bound: `exp (1/9) ≤ 9/8`. -/
lemma exp_one_ninth_le : Real.exp (1/9 : ℝ) ≤ 9/8 := by
  have h := one_sub_mul_exp_le_one (1/9)
  have h2 : (1 - (1:ℝ)/9) = 8/9 := by norm_num
  rw [h2] at h
  nlinarith [Real.exp_pos (1/9:ℝ)]

/-- For `0 < D` and `0 < n ≤ D`, there is a prime `p` such that for every
`1 ≤ k ≤ n`, `n · e^{k p/(9 D²)} + n · e^{k/(9 D²)} < p`.  This is the "house"
condition used in estimates for linear forms in logarithms. -/
theorem exists_prime_house_condition (D n : ℕ) (hD : 0 < D) (hn : 0 < n) (hnD : n ≤ D) :
    ∃ p : ℕ, Nat.Prime p ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n →
      (n : ℝ) * (Real.exp (1 / (9 * (D : ℝ) ^ 2))) ^ (k * p)
        + (n : ℝ) * (Real.exp (1 / (9 * (D : ℝ) ^ 2))) ^ k < (p : ℝ) := by
  -- Bertrand's postulate gives a prime in `(4n, 8n]`.
  obtain ⟨p, hpprime, hpgt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul (4 * n) (by omega)
  have hple' : p ≤ 8 * n := by omega
  refine ⟨p, hpprime, ?_⟩
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hden : (0:ℝ) < 9 * (D:ℝ)^2 := by positivity
  have hR := exp_one_ninth_le
  -- `exp (8/9) = (exp (1/9))^8 ≤ (9/8)^8`
  have hR8 : Real.exp (8/9 : ℝ) ≤ (9/8:ℝ)^8 := by
    have h : Real.exp (8/9:ℝ) = (Real.exp (1/9:ℝ))^8 := by
      rw [show (8/9:ℝ) = (8:ℕ) * (1/9) by norm_num, Real.exp_nat_mul]
    rw [h]
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hR 8
  have hnum : (9/8:ℝ)^8 + 9/8 < 4 := by norm_num
  intro k hk1 hkn
  -- `k * p ≤ 8 * D^2`
  have hkp_nat : k*p ≤ 8 * D^2 := by
    have h1 : k*p ≤ n*p := Nat.mul_le_mul_right p hkn
    have h2 : n*p ≤ n*(8*n) := Nat.mul_le_mul_left n hple'
    have h3 : n*(8*n) = 8*(n^2) := by ring
    have h4 : n^2 ≤ D^2 := Nat.pow_le_pow_left hnD 2
    calc k*p ≤ n*p := h1
      _ ≤ n*(8*n) := h2
      _ = 8*(n^2) := h3
      _ ≤ 8*(D^2) := Nat.mul_le_mul_left 8 h4
  have hkp : ((k*p : ℕ) : ℝ) ≤ 8 * (D:ℝ)^2 := by
    have hcast := Nat.cast_le (α := ℝ).2 hkp_nat
    push_cast at hcast ⊢
    exact hcast
  -- first factor: `(e^{1/(9D²)})^{k p} = e^{(kp)/(9D²)} ≤ e^{8/9}`
  have hfirst : (Real.exp (1/(9*(D:ℝ)^2)))^(k*p) ≤ Real.exp (8/9) := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    rw [mul_one_div, div_le_iff₀ hden]
    rw [show (8:ℝ)/9 * (9 * (D:ℝ)^2) = 8 * (D:ℝ)^2 by ring]
    exact hkp
  have hkD : (k:ℝ) ≤ (D:ℝ) := by
    have : k ≤ D := le_trans hkn hnD
    exact_mod_cast this
  -- second factor: `(e^{1/(9D²)})^k = e^{k/(9D²)} ≤ e^{1/9}`
  have hsecond : (Real.exp (1/(9*(D:ℝ)^2)))^k ≤ Real.exp (1/9) := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    rw [mul_one_div, div_le_iff₀ hden]
    rw [show (1:ℝ)/9 * (9 * (D:ℝ)^2) = (D:ℝ)^2 by ring]
    nlinarith [hkD, hD1]
  have hA := mul_le_mul_of_nonneg_left hfirst (le_of_lt hnR)
  have hB := mul_le_mul_of_nonneg_left hsecond (le_of_lt hnR)
  have hA8 := mul_le_mul_of_nonneg_left hR8 (le_of_lt hnR)
  have hB9 := mul_le_mul_of_nonneg_left hR (le_of_lt hnR)
  calc (n:ℝ) * (Real.exp (1/(9*(D:ℝ)^2)))^(k*p) + (n:ℝ)*(Real.exp (1/(9*(D:ℝ)^2)))^k
      ≤ (n:ℝ) * Real.exp (8/9) + (n:ℝ) * Real.exp (1/9) := add_le_add hA hB
    _ ≤ (n:ℝ) * (9/8)^8 + (n:ℝ) * (9/8) := add_le_add hA8 hB9
    _ = (n:ℝ) * ((9/8)^8 + 9/8) := by ring
    _ < (n:ℝ) * 4 := mul_lt_mul_of_pos_left hnum hnR
    _ = (4*n : ℝ) := by ring
    _ < (p:ℝ) := by exact_mod_cast hpgt

end Work.BW.es2
