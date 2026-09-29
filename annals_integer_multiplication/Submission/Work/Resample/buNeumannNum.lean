import Mathlib

namespace Work.Resample

/-- Numerical core of the Neumann-series tail bound: with `r = 2^{-a}`, `a ≥ 1` gives `r ≤ 1/2`, so
`(1/2)·(1-r)^{-1} ≤ 1` and `(1/2)·r^n/(1-r) ≤ r^n = 2^{-an} ≤ 2^{-p}` whenever `p ≤ a·n`. -/
theorem buNeumannNum (p n : ℕ) (a : ℝ) (ha : 1 ≤ a) (han : (p : ℝ) ≤ a * n) :
    (1 / 2) * (((2 : ℝ) ^ (-a)) ^ n / (1 - (2 : ℝ) ^ (-a))) ≤ 1 / (2 : ℝ) ^ p ∧
    (1 / 2) * (1 - (2 : ℝ) ^ (-a))⁻¹ ≤ 1 := by
  have h2pos : (0:ℝ) < 2 := by norm_num
  have h1lt2 : (1:ℝ) < 2 := by norm_num
  have hrpos : 0 < (2:ℝ)^(-a) := Real.rpow_pos_of_pos h2pos _
  -- `r = 2^{-a} ≤ 1/2` since `a ≥ 1` and `2^x` is increasing
  have hrle : (2:ℝ)^(-a) ≤ 1/2 := by
    have h : (2:ℝ)^(-a) ≤ (2:ℝ)^(-(1:ℝ)) := (Real.rpow_le_rpow_left_iff h1lt2).mpr (by linarith)
    have h2 : (2:ℝ)^(-(1:ℝ)) = 1/2 := by rw [Real.rpow_neg_one]; norm_num
    rw [h2] at h; exact h
  have h1mr_pos : 0 < 1 - (2:ℝ)^(-a) := by linarith
  have h1mr : (1/2:ℝ) ≤ 1 - (2:ℝ)^(-a) := by linarith
  -- `(1-r)^{-1} ≤ 2`
  have h2inv : (1 - (2:ℝ)^(-a))⁻¹ ≤ 2 := by
    have h := (inv_le_inv₀ h1mr_pos (by norm_num : (0:ℝ) < 1/2)).mpr h1mr
    rwa [show (1/2:ℝ)⁻¹ = 2 by norm_num] at h
  have hsecond : (1/2) * (1 - (2:ℝ)^(-a))⁻¹ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left h2inv (by norm_num : (0:ℝ) ≤ 1/2)
    linarith
  have hrn_nonneg : 0 ≤ ((2:ℝ)^(-a))^n := pow_nonneg (le_of_lt hrpos) n
  -- `r^n = 2^{-a n} ≤ 2^{-p}` since `p ≤ a n`
  have hrn : ((2:ℝ)^(-a))^n ≤ 2^(-(p:ℝ)) := by
    have hthis : ((2:ℝ)^(-a))^n = (2:ℝ)^((-a)*(n:ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [hthis]
    apply (Real.rpow_le_rpow_left_iff h1lt2).mpr
    nlinarith
  have hrpow_eq : (2:ℝ)^(-(p:ℝ)) = 1/(2:ℝ)^p := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast, one_div]
  refine ⟨?_, hsecond⟩
  calc (1/2) * (((2:ℝ)^(-a))^n / (1 - (2:ℝ)^(-a)))
      = ((2:ℝ)^(-a))^n * ((1/2) * (1 - (2:ℝ)^(-a))⁻¹) := by rw [div_eq_mul_inv]; ring
    _ ≤ ((2:ℝ)^(-a))^n * 1 := mul_le_mul_of_nonneg_left hsecond hrn_nonneg
    _ = ((2:ℝ)^(-a))^n := mul_one _
    _ ≤ 2^(-(p:ℝ)) := hrn
    _ = 1/(2:ℝ)^p := hrpow_eq

end Work.Resample
