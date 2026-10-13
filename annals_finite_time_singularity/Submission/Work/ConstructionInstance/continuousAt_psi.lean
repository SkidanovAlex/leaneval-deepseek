import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.ConstructionInstance.GCompDefs
import Submission.Work.Cyl.Frame

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

open Work.Cyl

/-! ## Continuity of the corrected angle `psi` off the axis

`psi x = arccos (r x / ρ x)` is the corrected polar angle of `GCompDefs`.  On the axis `x = 0`
it is genuinely discontinuous (the ratio `r/ρ` has no limit at the origin: it is `1` along the
plane `x₃ = 0` and `0` along the axis), which is why the hypothesis `x ≠ 0` below is exactly
what the geometry allows.  Off the axis `rho x > 0` and `psi` is a composition
`Real.arccos ∘ (r / ρ)` of continuous functions, both `radial` and `rho` being built out of the
smooth coordinate functions of `ℝ³`. -/

/-- **`psi` is continuous off the axis.**  For `x ≠ 0` the three-dimensional radius `rho x`
is nonzero, so `x ↦ radial x / rho x` is continuous at `x`, and `Real.arccos` is continuous
everywhere. -/
theorem continuousAt_psi {x : Work.ConstructionInstance.R3} (hx : x ≠ 0) :
    ContinuousAt Work.ConstructionInstance.psi x := by
  have hρ : Work.Cyl.rho x ≠ 0 := ne_of_gt ((Work.Cyl.rho_pos_iff x).mpr hx)
  have hrad : ContinuousAt (fun y : R3 => Work.Cyl.radial y) x := by
    unfold Work.Cyl.radial Work.Cyl.radSq
    fun_prop
  have hrhop : ContinuousAt (fun y : R3 => Work.Cyl.rho y) x := by
    unfold Work.Cyl.rho Work.Cyl.radSq Work.Cyl.axial
    fun_prop
  have hdiv : ContinuousAt (fun y : R3 => Work.Cyl.radial y / Work.Cyl.rho y) x :=
    hrad.div hrhop hρ
  have hcomp := Real.continuous_arccos.continuousAt.comp hdiv
  unfold Work.ConstructionInstance.psi
  exact hcomp

end Work.ConstructionInstance
