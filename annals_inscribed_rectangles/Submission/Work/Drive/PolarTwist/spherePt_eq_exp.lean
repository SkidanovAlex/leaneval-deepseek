import Mathlib
import Submission.Work.OneDim.CirclePtFacts
import Submission.Work.Drive.PolarTwist.radialGraph_flat

/-!
# The stereographic coordinate `spherePt'` in terms of the angle

`Work.OneDim.spherePt' v` is the point of the unit circle with complex coordinates
`((v^2 - 1)/(1 + v^2), 2v/(1 + v^2))`.  Since `2 arctan v` is the angle with
`cos (2 arctan v) = (1 - v^2)/(1 + v^2)` and `sin (2 arctan v) = 2v/(1 + v^2)`
(the Weierstrass substitution `v = tan (θ/2)`), this point is
`(cos (π - 2 arctan v), sin (π - 2 arctan v))`, i.e. `Circle.exp (π - 2 arctan v)`.

The identity is what lets the stereographic chart be replaced by the angle chart
whenever a map built out of `spherePt'` has to be compared with a rotation.
-/

namespace Work.Drive.PolarTwist

open scoped ContDiff

noncomputable section

/-- The Weierstrass substitution: `cos (2 arctan v) = (1 - v^2)/(1 + v^2)`. -/
theorem cos_two_arctan (v : ℝ) : Real.cos (2 * Real.arctan v) = (1 - v ^ 2) / (1 + v ^ 2) := by
  rw [Real.cos_two_mul, Real.cos_arctan]
  have hsq : (Real.sqrt (1 + v ^ 2)) ^ 2 = 1 + v ^ 2 := Real.sq_sqrt (by positivity)
  have hne : Real.sqrt (1 + v ^ 2) ≠ 0 := by positivity
  field_simp
  nlinarith [hsq]

/-- The Weierstrass substitution: `sin (2 arctan v) = 2v/(1 + v^2)`. -/
theorem sin_two_arctan (v : ℝ) : Real.sin (2 * Real.arctan v) = 2 * v / (1 + v ^ 2) := by
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  have hsq : (Real.sqrt (1 + v ^ 2)) ^ 2 = 1 + v ^ 2 := Real.sq_sqrt (by positivity)
  have hne : Real.sqrt (1 + v ^ 2) ≠ 0 := by positivity
  field_simp
  rw [hsq]

theorem spherePt_eq_exp (v : ℝ) :
    Work.OneDim.spherePt' v = Circle.exp (Real.pi - 2 * Real.arctan v) := by
  refine Work.OneDim.circle_ext' ?_ ?_
  · rw [Work.OneDim.spherePt'_coe, Circle.coe_exp, Complex.exp_ofReal_mul_I]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    rw [Real.cos_pi_sub, cos_two_arctan]
    ring
  · rw [Work.OneDim.spherePt'_coe, Circle.coe_exp, Complex.exp_ofReal_mul_I]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, add_zero]
    rw [zero_add, zero_add, Real.sin_pi_sub, sin_two_arctan]

end

end Work.Drive.PolarTwist
