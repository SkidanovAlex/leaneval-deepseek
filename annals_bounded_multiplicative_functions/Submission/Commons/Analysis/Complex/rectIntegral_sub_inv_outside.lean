import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex MeasureTheory intervalIntegral MeromorphicOn
open scoped Real Interval Topology
set_option autoImplicit false
noncomputable section

namespace Commons.Analysis.Complex

/-- Residue of `(s-u)⁻¹` around the rectangle boundary (same left-hand side as
`rectIntegral_sub_inv_inside`) vanishes when `u` is strictly outside the closed rectangle:
`u.re < z.re`, `w.re < u.re`, `u.im < z.im`, or `w.im < u.im`.

Then `s ↦ (s-u)⁻¹` is complex differentiable on a neighbourhood of the closed rectangle
`(z.re..w.re) × (z.im..w.im)`, so the integral vanishes by
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`. -/
theorem rectIntegral_sub_inv_outside {z w u : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huout : u.re < z.re ∨ w.re < u.re ∨ u.im < z.im ∨ w.im < u.im) :
    (∫ x : ℝ in z.re..w.re, (((x : ℂ) + (z.im : ℂ) * Complex.I) - u)⁻¹) -
        (∫ x : ℝ in z.re..w.re, (((x : ℂ) + (w.im : ℂ) * Complex.I) - u)⁻¹) +
        Complex.I • (∫ y : ℝ in z.im..w.im, (((w.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹) -
        Complex.I • (∫ y : ℝ in z.im..w.im, (((z.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹) =
        0 := by
  let f : ℂ → ℂ := fun s => (s - u)⁻¹
  have hdiff : DifferentiableOn ℂ f (Complex.Rectangle z w) := by
    intro s hs
    have hsreI : s.re ∈ Set.Icc z.re w.re := by
      rw [← Set.uIcc_of_le hzre.le]
      exact (Complex.mem_reProdIm.mp hs).1
    have hsimI : s.im ∈ Set.Icc z.im w.im := by
      rw [← Set.uIcc_of_le hzim.le]
      exact (Complex.mem_reProdIm.mp hs).2
    have hsne : s ≠ u := by
      rcases huout with h | h | h | h
      · exact fun hsu => (ne_of_lt (lt_of_lt_of_le h hsreI.1)) (congrArg Complex.re hsu).symm
      · exact fun hsu => (ne_of_gt (lt_of_le_of_lt hsreI.2 h)) (congrArg Complex.re hsu).symm
      · exact fun hsu => (ne_of_lt (lt_of_lt_of_le h hsimI.1)) (congrArg Complex.im hsu).symm
      · exact fun hsu => (ne_of_gt (lt_of_le_of_lt hsimI.2 h)) (congrArg Complex.im hsu).symm
    refine ((hasDerivAt_inv (sub_ne_zero.mpr hsne)).differentiableAt.comp s ?_).differentiableWithinAt
    fun_prop
  simpa [f] using
    (Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hdiff)

end Commons.Analysis.Complex
