import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

lemma PayMonomials (a M R ρ Y C : ℝ) (ha : 0 ≤ a) (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hY : 0 ≤ Y) (hρR : ρ ≤ R) (hR : 0 < R) (hC : 256 ≤ C) :
    256 * ρ * a * (M + Real.sqrt (M * R * Y))
      ≤ C * (R * a * M + R ^ (3 / 2 : ℝ) * a * Real.sqrt (Y * M)) := by
  have hR0 : (0 : ℝ) ≤ R := le_of_lt hR
  -- the two elementary identities that make the two sides match at constant 256
  have hsqrt : Real.sqrt (M * R * Y) = Real.sqrt R * Real.sqrt (Y * M) := by
    rw [show M * R * Y = R * (Y * M) by ring]
    rw [Real.sqrt_mul hR0]
  have hpow : R ^ (3 / 2 : ℝ) = R * Real.sqrt R := by
    have h : R ^ (3 / 2 : ℝ) = R ^ (1 : ℝ) * R ^ (1 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hR]
    rw [h, Real.rpow_one, ← Real.sqrt_eq_rpow]
  -- ρ ≤ R, multiplied by the two nonnegative monomials
  have h1 : ρ * (a * M) ≤ R * (a * M) := mul_le_mul_of_nonneg_right hρR (mul_nonneg ha hM)
  have h2 : ρ * (a * (Real.sqrt R * Real.sqrt (Y * M)))
      ≤ R * (a * (Real.sqrt R * Real.sqrt (Y * M))) :=
    mul_le_mul_of_nonneg_right hρR (by positivity)
  have hmain : ρ * a * (M + Real.sqrt (M * R * Y))
      ≤ R * a * M + R ^ (3 / 2 : ℝ) * a * Real.sqrt (Y * M) := by
    rw [mul_add, hsqrt, hpow]
    nlinarith [h1, h2]
  have hb : 0 ≤ R * a * M + R ^ (3 / 2 : ℝ) * a * Real.sqrt (Y * M) := by
    have h3 : (0 : ℝ) ≤ R ^ (3 / 2 : ℝ) := Real.rpow_nonneg hR0 _
    have h4 : (0 : ℝ) ≤ Real.sqrt (Y * M) := Real.sqrt_nonneg _
    positivity
  calc 256 * ρ * a * (M + Real.sqrt (M * R * Y))
      = 256 * (ρ * a * (M + Real.sqrt (M * R * Y))) := by ring
    _ ≤ 256 * (R * a * M + R ^ (3 / 2 : ℝ) * a * Real.sqrt (Y * M)) :=
        mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ ≤ C * (R * a * M + R ^ (3 / 2 : ℝ) * a * Real.sqrt (Y * M)) :=
        mul_le_mul_of_nonneg_right hC hb

end Work.BoseFixR
