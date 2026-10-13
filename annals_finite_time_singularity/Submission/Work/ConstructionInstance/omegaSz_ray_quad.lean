import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **The self-similar vorticity on the ray `x = (t,0,t)`, at a prescribed self-similar variable.**

On this ray (`t > 0`) one has `r = t`, `θ = arctan 1 = π/4` and `e_θ = e₁ = (0,1,0)`, so
`omegaSz p g z x = profile p g z (θ x) • e_θ(x) = profile p g z (π/4) • e₁`. -/
theorem omegaSz_ray_quad {p z t : ℝ} (ht : 0 < t) (g : ℝ → ℝ → ℝ) :
    Work.ConstructionInstance.omegaSz p g z (!₂[t, 0, t] : Work.ConstructionInstance.R3)
      = Work.ConstructionInstance.profile p g z (Real.pi / 4)
        • (!₂[0, 1, 0] : Work.ConstructionInstance.R3) := by
  -- `θ = arctan(t/t) = arctan 1 = π/4`.
  have htheta : Work.Cyl.theta (!₂[t, 0, t] : R3) = Real.pi / 4 := by
    rw [Work.Cyl.theta, Work.Cyl.axial, Work.Cyl.radial, Work.Cyl.radSq]
    simp
    rw [Real.sqrt_sq ht.le, div_self (ne_of_gt ht)]
  -- `e_θ = (-x₁, x₀, 0)/r = (0,1,0) = e₁`.
  have he : Work.Cyl.eTheta (!₂[t, 0, t] : R3) = (!₂[0, 1, 0] : R3) := by
    refine Work.Cyl.ext_coord ?_ ?_ ?_ <;>
      simp [Work.Cyl.eTheta, Work.Cyl.angularVec, Work.Cyl.radial, Work.Cyl.radSq,
        Real.sqrt_sq ht.le, ht.ne']
  rw [omegaSz_apply, htheta, he]

end Work.ConstructionInstance
