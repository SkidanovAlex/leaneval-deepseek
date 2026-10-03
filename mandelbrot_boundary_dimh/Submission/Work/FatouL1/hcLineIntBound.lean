import Mathlib

namespace Work.FatouL1

/-- Cauchy-type estimate along a vertical line: if the line mass of `‖h‖` over the line
`{L + i y}` is at most `M`, then the (Bochner) integral of `h(ζ)/(ζ - z)` along that line is at
most `M` divided by the distance `|L - z.re|` from `z` to the line. -/
theorem hcLineIntBound {h : ℂ → ℂ} {L : ℝ} {z : ℂ} {M : ℝ}
    (hI : MeasureTheory.Integrable (fun y : ℝ => h ((L : ℂ) + y * Complex.I)))
    (hlin : ∫ y : ℝ, ‖h ((L : ℂ) + y * Complex.I)‖ ≤ M) (hM : 0 ≤ M) (hz : L ≠ z.re) :
    ‖∫ y : ℝ, h ((L : ℂ) + y * Complex.I) / (((L : ℂ) + y * Complex.I) - z)‖ ≤ M / |L - z.re| := by
  have hcpos : 0 < |L - z.re| := abs_pos.mpr (sub_ne_zero.mpr hz)
  -- the distance from `z` to the line is a lower bound for the denominator
  have hden : ∀ y : ℝ, |L - z.re| ≤ ‖((L : ℂ) + y * Complex.I) - z‖ := by
    intro y
    have hre : (((L : ℂ) + y * Complex.I) - z).re = L - z.re := by simp
    calc |L - z.re| = |(((L : ℂ) + y * Complex.I) - z).re| := by rw [hre]
      _ ≤ ‖((L : ℂ) + y * Complex.I) - z‖ := Complex.abs_re_le_norm _
  have hnorm : MeasureTheory.Integrable (fun y : ℝ => ‖h ((L : ℂ) + y * Complex.I)‖) := hI.norm
  have hC : MeasureTheory.Integrable
      (fun y : ℝ => |L - z.re|⁻¹ * ‖h ((L : ℂ) + y * Complex.I)‖) := hnorm.const_mul _
  -- pointwise bound of the integrand's norm by the scaled line mass
  have hpt : ∀ y : ℝ,
      ‖h ((L : ℂ) + y * Complex.I) / (((L : ℂ) + y * Complex.I) - z)‖
        ≤ |L - z.re|⁻¹ * ‖h ((L : ℂ) + y * Complex.I)‖ := by
    intro y
    rw [norm_div]
    calc ‖h ((L : ℂ) + y * Complex.I)‖ / ‖((L : ℂ) + y * Complex.I) - z‖
        ≤ ‖h ((L : ℂ) + y * Complex.I)‖ / |L - z.re| :=
          div_le_div_of_nonneg_left (norm_nonneg _) hcpos (hden y)
      _ = |L - z.re|⁻¹ * ‖h ((L : ℂ) + y * Complex.I)‖ := by rw [div_eq_inv_mul]
  have hMabs : 0 ≤ M / |L - z.re| := div_nonneg hM (abs_nonneg _)
  calc ‖∫ y : ℝ, h ((L : ℂ) + y * Complex.I) / (((L : ℂ) + y * Complex.I) - z)‖
      ≤ ∫ y : ℝ, ‖h ((L : ℂ) + y * Complex.I) / (((L : ℂ) + y * Complex.I) - z)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, |L - z.re|⁻¹ * ‖h ((L : ℂ) + y * Complex.I)‖ :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun y => norm_nonneg _)) hC
          (Filter.Eventually.of_forall hpt)
    _ = |L - z.re|⁻¹ * ∫ y : ℝ, ‖h ((L : ℂ) + y * Complex.I)‖ :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ |L - z.re|⁻¹ * M := mul_le_mul_of_nonneg_left hlin (inv_nonneg.mpr hcpos.le)
    _ = M / |L - z.re| := by rw [div_eq_mul_inv, mul_comm]

end Work.FatouL1
