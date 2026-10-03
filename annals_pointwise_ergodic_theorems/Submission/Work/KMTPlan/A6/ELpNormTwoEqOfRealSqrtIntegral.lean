import Mathlib

namespace Work.KMTPlan.A6

/-- For a Schwartz function `f : ℝ → ℂ` the `L²` seminorm (as an `ℝ≥0∞`) equals the
`ofReal` of the real square root of `∫ t, ‖f t‖ ^ 2`.

This is the `p = 2` case of `MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm` (with the
Bochner integral over `volume`), together with `Real.sqrt_eq_rpow` (`√x = x ^ (1/2)`) and
`ENNReal.toReal 2 = 2`.  The `MemLp` hypothesis is supplied by `SchwartzMap.memLp`. -/
theorem ELpNormTwoEqOfRealSqrtIntegral (f : SchwartzMap ℝ ℂ) :
    MeasureTheory.eLpNorm (f : ℝ → ℂ) 2 MeasureTheory.volume
      = ENNReal.ofReal (Real.sqrt (∫ t : ℝ, ‖(f : ℝ → ℂ) t‖ ^ 2)) := by
  rw [MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm (μ := MeasureTheory.volume)
    (f := (f : ℝ → ℂ)) (p := 2) (by norm_num) (by norm_num)
    (f.memLp 2 MeasureTheory.volume)]
  rw [ENNReal.toReal_ofNat]
  congr 1
  rw [Real.sqrt_eq_rpow, one_div]
  congr 1
  simp

end Work.KMTPlan.A6
