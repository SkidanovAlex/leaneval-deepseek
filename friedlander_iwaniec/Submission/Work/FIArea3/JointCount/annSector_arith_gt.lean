import Mathlib

namespace Work.FIArea3.JointCount

theorem annSector_arith_gt (a θ r : ℝ) (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hr0 : 0 ≤ r)
    (hr2 : r ≤ 1.2 * θ * a) (har : a ≤ r) :
    Real.pi * (a * Real.sqrt (1 + θ) + r) ^ 2 ≤ Real.pi * (θ * a) ^ 2 + 32 * (θ * a) * r := by
  have ha0 : 0 ≤ a := le_of_lt ha
  -- √(1+θ) ≤ 3/2
  have hs : Real.sqrt (1 + θ) ≤ 3 / 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith [hθ1]
  -- a√(1+θ) ≤ (3/2) r
  have hprod : a * Real.sqrt (1 + θ) ≤ (3 / 2) * r := by
    have h1 : a * Real.sqrt (1 + θ) ≤ a * (3 / 2) := mul_le_mul_of_nonneg_left hs ha0
    nlinarith [har, h1]
  have hsum : a * Real.sqrt (1 + θ) + r ≤ (5 / 2) * r := by linarith
  have hsq : (a * Real.sqrt (1 + θ) + r) ^ 2 ≤ ((5 / 2) * r) ^ 2 := by
    refine sq_le_sq' ?_ hsum
    have hnn : 0 ≤ a * Real.sqrt (1 + θ) := by
      have := Real.sqrt_nonneg (1 + θ)
      nlinarith [ha0, this]
    linarith
  have hL : Real.pi * (a * Real.sqrt (1 + θ) + r) ^ 2 ≤ Real.pi * ((5 / 2) * r) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq Real.pi_nonneg
  -- lower bound for the right side
  have hA : (5 / 6) * r ≤ θ * a := by nlinarith [hr2]
  have hR : 80 / 3 * r ^ 2 ≤ 32 * (θ * a) * r := by
    have h1 := mul_le_mul_of_nonneg_right hA hr0
    nlinarith [h1]
  have hR2 : 80 / 3 * r ^ 2 ≤ Real.pi * (θ * a) ^ 2 + 32 * (θ * a) * r := by
    have hpi2 : 0 ≤ Real.pi * (θ * a) ^ 2 := by positivity
    linarith
  -- numeric core
  have hfin : Real.pi * ((5 / 2) * r) ^ 2 ≤ 80 / 3 * r ^ 2 := by
    have hpi25 : Real.pi * (25 / 4) ≤ 80 / 3 := by nlinarith [Real.pi_lt_d20]
    calc Real.pi * ((5 / 2) * r) ^ 2 = Real.pi * (25 / 4) * r ^ 2 := by ring
      _ ≤ 80 / 3 * r ^ 2 := mul_le_mul_of_nonneg_right hpi25 (sq_nonneg r)
  exact le_trans hL (le_trans hfin hR2)

end Work.FIArea3.JointCount
