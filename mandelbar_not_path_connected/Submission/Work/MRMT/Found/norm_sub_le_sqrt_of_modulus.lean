import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- If `‖z - x‖ ≤ δ` with `0 < δ ≤ 1/4`, then the modulus bound
`‖φ z - φ x‖ ^ 2 ≤ C / log (1 / ‖z - x‖)` upgrades to the (weakly weaker) bound
`‖φ z - φ x‖ ≤ sqrt (C / log (1 / δ))`, because `t ↦ log (1 / t)` is decreasing
and `log (1/δ) > 0`.  (The case `‖z - x‖ = 0` is handled separately, since
`log 0 = 0` in the Mathlib convention.) -/
theorem norm_sub_le_sqrt_of_modulus {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    {φ : ℂ → ℂ} {x z : ℂ} (hz : ‖z - x‖ ≤ δ)
    (h : ‖φ z - φ x‖ ^ 2 ≤ C / Real.log (1 / ‖z - x‖)) :
    ‖φ z - φ x‖ ≤ Real.sqrt (C / Real.log (1 / δ)) := by
  have hδlt : δ < 1 := by linarith
  have hlogδ_pos : 0 < Real.log (1 / δ) := Real.log_pos (one_lt_one_div hδ hδlt)
  by_cases hz0 : ‖z - x‖ = 0
  · -- degenerate case: log (1/0) = log 0 = 0, so C / log (1/0) = 0
    have h2 : ‖φ z - φ x‖ ^ 2 ≤ 0 := by
      have hh := h
      simp only [hz0, div_zero, Real.log_zero] at hh
      exact hh
    have hn0 : ‖φ z - φ x‖ = 0 := by nlinarith [norm_nonneg (φ z - φ x)]
    rw [hn0]
    exact Real.sqrt_nonneg _
  · have hzpos : 0 < ‖z - x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0)
    have h1δ : 1 / δ ≤ 1 / ‖z - x‖ := one_div_le_one_div_of_le hzpos hz
    have hlog_le : Real.log (1 / δ) ≤ Real.log (1 / ‖z - x‖) :=
      Real.log_le_log (by positivity) h1δ
    have hC' : C / Real.log (1 / ‖z - x‖) ≤ C / Real.log (1 / δ) :=
      div_le_div_of_nonneg_left hC.le hlogδ_pos hlog_le
    have h2 : ‖φ z - φ x‖ ^ 2 ≤ C / Real.log (1 / δ) := le_trans h hC'
    calc ‖φ z - φ x‖ = Real.sqrt (‖φ z - φ x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (C / Real.log (1 / δ)) := Real.sqrt_le_sqrt h2

end Work.MRMT.Found
