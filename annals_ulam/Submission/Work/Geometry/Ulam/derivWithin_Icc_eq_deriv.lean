import Mathlib

namespace Commons.Geometry.Ulam

open MeasureTheory Set Filter
open scoped ContDiff Pointwise Interval Topology

set_option autoImplicit false

/-- One-sided/global derivative link at an arbitrary point of `[0, π/2]`. -/
lemma derivWithin_Icc_eq_deriv_of_differentiableAt'
    {R : ℝ → ℝ} {x : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.pi / 2))
    (hR_diff : DifferentiableAt ℝ R x) :
    derivWithin R (Set.Icc 0 (Real.pi / 2)) x = deriv R x := by
  have hzero_pi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hU : UniqueDiffOn ℝ (Set.Icc 0 (Real.pi / 2)) := uniqueDiffOn_Icc hzero_pi
  have hxU : UniqueDiffWithinAt ℝ (Set.Icc 0 (Real.pi / 2)) x := hU.uniqueDiffWithinAt hx
  unfold derivWithin deriv
  rw [fderivWithin_eq_fderiv hxU hR_diff]

/-- Specialisation to the left endpoint. -/
lemma derivWithin_Icc_eq_deriv_of_differentiableAt
    {R : ℝ → ℝ} (hR_diff : DifferentiableAt ℝ R 0) :
    derivWithin R (Set.Icc 0 (Real.pi / 2)) 0 = deriv R 0 :=
  derivWithin_Icc_eq_deriv_of_differentiableAt'
    (by constructor <;> linarith [Real.pi_pos]) hR_diff

/-- Specialisation to the right endpoint. -/
lemma derivWithin_Icc_eq_deriv_at_pi_div_two_of_differentiableAt
    {R : ℝ → ℝ} (hR_diff : DifferentiableAt ℝ R (Real.pi / 2)) :
    derivWithin R (Set.Icc 0 (Real.pi / 2)) (Real.pi / 2) = deriv R (Real.pi / 2) :=
  derivWithin_Icc_eq_deriv_of_differentiableAt'
    (by constructor <;> linarith [Real.pi_pos]) hR_diff

end Commons.Geometry.Ulam
