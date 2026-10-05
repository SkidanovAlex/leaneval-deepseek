import Mathlib
import Submission.Work.RPV.Defs

/-!
# B1: the signed-area functional and the winding display of a closed plane curve

This file holds the two definitions shared by the pieces of the proof of
`Work.RPB.B1.area_pos_of_isotopy_infty`: the signed-area functional
`areaInt c = ∮ ω_ℂ(c, c')` and the "winding display"
`windDisp c z = (1/π) ∫ Im (c' / (c - z))`, which is (twice) the winding number of the closed
curve `c` about the point `z` (and is set to `0` on the curve itself).

The main input the assembly needs is the **area formula** `areaInt c = ∫ z, windDisp c z`
(the signed area is the integral of the winding number), together with the identification of
`windDisp` with the degree-based winding number of the ported tree
(`Work.RPB.Port.Drive.winding`).
-/

open scoped ContDiff Interval

set_option autoImplicit false

namespace Work.RPB.B1

noncomputable section

/-- The signed-area integral `∮ ω_ℂ(c, c') = ∫₀^{2π} ω_ℂ(c t, c' t)` of a plane curve. -/
def areaInt (c : ℝ → ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..(2 * Real.pi), Work.RPV.ωC (c t) (deriv c t)

/-- The **winding display** of a plane curve `c`: `(1/π) ∫₀^{2π} Im (c'(s) / (c(s) - z))`, i.e.
twice the winding number of `c` about `z`.  On the curve itself (a set of measure zero) the value
is set to `0`. -/
def windDisp (c : ℝ → ℂ) (z : ℂ) : ℝ := by
  classical
  exact if z ∈ Set.range c then 0
    else (1 / Real.pi) * ∫ s in (0 : ℝ)..(2 * Real.pi), ((deriv c s) / (c s - z)).im

@[simp] lemma areaInt_def (c : ℝ → ℂ) :
    areaInt c = ∫ t in (0 : ℝ)..(2 * Real.pi), Work.RPV.ωC (c t) (deriv c t) := rfl

end

end Work.RPB.B1
