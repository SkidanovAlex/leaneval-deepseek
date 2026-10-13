import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.Coords

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- The unit angular vector `x ↦ e_θ(x)` is continuous at every point off the axis.

`e_θ = (1/r) • angularVec` with `angularVec x = (-x₁, x₀, 0)` a continuous (indeed linear) map
and `r = √(x₀²+x₁²)` continuous and nonvanishing at `x`. -/
theorem continuousAt_eTheta_of_radial_ne_zero {x : Work.Cyl.R3}
    (hx : Work.Cyl.radial x ≠ 0) : ContinuousAt Work.Cyl.eTheta x := by
  have hrad : ContinuousAt (fun y : Work.Cyl.R3 => Work.Cyl.radial y) x := by
    unfold Work.Cyl.radial Work.Cyl.radSq
    fun_prop
  have hang : ContinuousAt (fun y : Work.Cyl.R3 => Work.Cyl.angularVec y) x := by
    rw [show Work.Cyl.angularVec =
        fun y : Work.Cyl.R3 => (-y 1) • Work.Cyl.e0 + (y 0) • Work.Cyl.e1 from by
      funext y
      apply Work.Cyl.ext_coord <;>
        simp [Work.Cyl.angularVec, Work.Cyl.e0, Work.Cyl.e1, FiniteTimeSingularity.e]]
    fun_prop
  have hinv : ContinuousAt (fun y : Work.Cyl.R3 => (Work.Cyl.radial y)⁻¹) x :=
    hrad.inv₀ hx
  have hsmul : ContinuousAt (fun y : Work.Cyl.R3 =>
      (Work.Cyl.radial y)⁻¹ • Work.Cyl.angularVec y) x := hinv.smul hang
  convert hsmul using 1
  funext y
  rw [Work.Cyl.eTheta, one_div]

end Work.ConstructionInstance
