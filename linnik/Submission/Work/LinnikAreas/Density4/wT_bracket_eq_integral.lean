import Mathlib
import Submission.Work.Analysis.Integral.trig_conv_integral

namespace Work.LinnikAreas.Density4

/-- The bracket expression of HB's test function `fT` equals the convolution integral
`∫_{s-θ}^{θ} (cos v - cos θ)(cos(s-v) - cos θ) dv`.

This is the specialisation `z = 1`, `g = θ`, `x = s` of the general trigonometric
convolution identity `Work.Analysis.Integral.trig_conv_integral`. -/
theorem wT_bracket_eq_integral (θ s : ℝ) :
    (2 * θ - s) * (Real.cos s / 2 + Real.cos θ ^ 2) + Real.sin (2 * θ - s) / 2
        - Real.sin (2 * θ) + 2 * Real.cos θ * Real.sin (s - θ)
      = ∫ v in (s - θ)..θ,
          (Real.cos v - Real.cos θ) * (Real.cos (s - v) - Real.cos θ) := by
  have h := Work.Analysis.Integral.trig_conv_integral 1 θ θ s (by norm_num) (by ring)
  simpa using h.symm

end Work.LinnikAreas.Density4
