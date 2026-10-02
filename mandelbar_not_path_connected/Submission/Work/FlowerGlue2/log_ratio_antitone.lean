import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

theorem log_ratio_antitone {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (1 + Real.log b) / b ≤ (1 + Real.log a) / a := by
  have ha_pos : 0 < a := lt_of_lt_of_le one_pos ha
  have hb_pos : 0 < b := lt_of_lt_of_le one_pos (le_trans ha hab)
  have hlog_a : 0 ≤ Real.log a := Real.log_nonneg ha
  -- Key estimate: `a * log b - b * log a ≤ b - a`.
  -- It follows from `log (b / a) ≤ b / a - 1` multiplied by `a > 0`.
  have key : a * Real.log b - b * Real.log a ≤ b - a := by
    have hba : 0 < b / a := div_pos hb_pos ha_pos
    have h1 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos hba
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt ha_pos)
    rw [Real.log_div hb_pos.ne' ha_pos.ne'] at h2
    have h3 : a * (b / a - 1) = b - a := by field_simp
    have h4 : 0 ≤ (b - a) * Real.log a := mul_nonneg (by linarith) hlog_a
    rw [h3] at h2
    nlinarith [h2, h4]
  rw [div_le_div_iff₀ hb_pos ha_pos]
  nlinarith [key]

end Work.FlowerGlue2
