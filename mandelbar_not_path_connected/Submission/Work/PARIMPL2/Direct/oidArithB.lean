import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

theorem oidArithB (R cr : ℝ) (hR : 128 ≤ R) (hcr : |cr| ≤ 3 * R / 32 + 81 / 64) :
    30 + |cr| * (3 + 4 / R) * (24 / R) ≤ 8 * (1 + Real.log R) := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hb : (0 : ℝ) ≤ 3 + 4 / R := by positivity
  have hc : (0 : ℝ) ≤ 24 / R := by positivity
  -- monotone replacement of |cr| by its bound
  have hmono : |cr| * (3 + 4 / R) * (24 / R)
      ≤ (3 * R / 32 + 81 / 64) * (3 + 4 / R) * (24 / R) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcr hb) hc
  -- closed form of the bound
  have hS : (3 * R / 32 + 81 / 64) * (3 + 4 / R) * (24 / R)
      = 27 / 4 + 801 / (8 * R) + 243 / (2 * R ^ 2) := by
    field_simp
    ring
  -- numeric upper bound for the bound at R ≥ 128
  have hbnd : 115 / 4 + 801 / (8 * R) + 243 / (2 * R ^ 2) ≤ 967955 / 32768 := by
    field_simp
    nlinarith [hR]
  -- lower bound on log R
  have hlog : (967955 / 262144 : ℝ) < Real.log R := by
    have h1 : Real.log 128 ≤ Real.log R := Real.log_le_log (by norm_num) hR
    have h2 : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
      norm_num
    have h3 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    nlinarith [h1, h2, h3]
  have hkey : 30 + (3 * R / 32 + 81 / 64) * (3 + 4 / R) * (24 / R)
      ≤ 8 * (1 + Real.log R) := by
    rw [hS]
    nlinarith [hbnd, hlog]
  linarith [hmono, hkey]

end Work.PARIMPL2.Direct
