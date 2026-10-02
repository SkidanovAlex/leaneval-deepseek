import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- Elementary arithmetic estimate used in the Mandelbar (tricorn) scaling argument:
for `R ≥ 128` and `|cr| ≤ 3R/32 + 81/64` we have
`14 * (exp (12 |cr| / R) - 1) ≤ 8 * (1 + log R)`. -/
theorem oidcnArith (R cr : ℝ) (hR : 128 ≤ R) (hcr : |cr| ≤ 3 * R / 32 + 81 / 64) :
    14 * (Real.exp (12 * |cr| / R) - 1) ≤ 8 * (1 + Real.log R) := by
  have hRpos : (0:ℝ) < R := by linarith
  -- Step 1: the exponent `12 * |cr| / R` is at most `5/4`.
  have ha_le : 12 * |cr| / R ≤ 5 / 4 := by
    have h1 : 12 * |cr| ≤ 12 * (3 * R / 32 + 81 / 64) := by linarith [hcr]
    have h2 : 12 * |cr| / R ≤ 12 * (3 * R / 32 + 81 / 64) / R :=
      div_le_div_of_nonneg_right h1 (le_of_lt hRpos)
    have h3 : 12 * (3 * R / 32 + 81 / 64) / R ≤ 5 / 4 := by
      rw [div_le_iff₀ hRpos]
      nlinarith [hR]
    linarith
  -- Step 2: hence `exp (12 |cr| / R) ≤ exp (5/4) ≤ 4`.
  have hExp : Real.exp (12 * |cr| / R) ≤ 4 := by
    have h54 : Real.exp (5/4 : ℝ) ≤ 4 := by
      have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        have : (4:ℝ) = 2^2 := by norm_num
        rw [this, Real.log_pow]; norm_num
      have h5 : (5/4:ℝ) ≤ Real.log 4 := by rw [h4]; linarith
      calc Real.exp (5/4:ℝ) ≤ Real.exp (Real.log 4) := Real.exp_le_exp.mpr h5
        _ = 4 := Real.exp_log (by norm_num)
    calc Real.exp (12 * |cr| / R) ≤ Real.exp (5/4) := Real.exp_le_exp.mpr ha_le
      _ ≤ 4 := h54
  -- Step 3: `log R ≥ log 128 = 7 log 2 > 34/8`, so the right hand side is at least 42.
  have hlogR : Real.log 128 ≤ Real.log R := Real.log_le_log (by norm_num) hR
  have h128 : Real.log 128 = 7 * Real.log 2 := by
    have : (128:ℝ) = 2^7 := by norm_num
    rw [this, Real.log_pow]; norm_num
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  calc 14 * (Real.exp (12 * |cr| / R) - 1) ≤ 14 * (4 - 1) := by linarith
    _ = 42 := by norm_num
    _ ≤ 8 * (1 + Real.log R) := by rw [h128] at hlogR; linarith

end Work.PARIMPL2.Direct
