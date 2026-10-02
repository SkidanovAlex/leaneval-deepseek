import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Cauchy

/-- **The radial weight `(1 + ‖z‖²)⁻²` is integrable on `ℂ`.**

This is the dimension-2 case of the Japanese-bracket integrability criterion
`integrable_rpow_neg_one_add_norm_sq`: since `finrank ℝ ℂ = 2 < 4`, the function
`z ↦ (1 + ‖z‖²) ^ (-4/2)` is integrable, and `-4/2 = -2` together with
`a ^ (-2) = 1 / a ^ 2` identifies it with `z ↦ 1 / (1 + ‖z‖²) ^ 2`.  Lifting the
real-valued integrability to `ℂ` is `MeasureTheory.Integrable.ofReal`. -/
theorem integrable_one_div_one_add_normSq_sq :
    MeasureTheory.Integrable (fun z : ℂ => ((1 / (1 + ‖z‖ ^ 2) ^ 2 : ℝ) : ℂ))
      MeasureTheory.volume := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := MeasureTheory.volume) (r := 4)
    (by rw [Complex.finrank_real_complex]; norm_num)
  refine (h.ofReal).congr ?_
  filter_upwards with z
  rw [show ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(4 : ℝ) / 2) = 1 / (1 + ‖z‖ ^ 2) ^ 2 from by
    have hpos : (0 : ℝ) ≤ 1 + ‖z‖ ^ 2 := by positivity
    rw [show (-(4 : ℝ) / 2) = -(2 : ℝ) by norm_num, Real.rpow_neg hpos, Real.rpow_two,
      one_div]]
  rfl

end Work.MRMT.Cauchy
