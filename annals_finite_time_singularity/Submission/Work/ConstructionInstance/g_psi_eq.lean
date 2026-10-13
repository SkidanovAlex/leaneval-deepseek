import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.ConstructionInstance.GCompDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- Off the symmetry axis `psi` agrees with `|theta|` (`psi_eq_abs_theta`), and on the axis
`psi = π/2` while `|theta| = |arctan (x₃/0)| = 0`; at both `θ = 0` and `θ = π/2` the profile `g`
vanishes on the whole angular boundary by `VanishTheta`.  Hence the composite
`g (ρ^{3α}) (·)` takes the same value at `|theta x|` and at `psi x`. -/
theorem g_psi_eq {α : ℝ} {g : ℝ → ℝ → ℝ} (hquad0 : ∀ θ : ℝ, g 0 θ = 0)
    (hvt : Work.Spaces.VanishTheta g) (x : R3) :
    g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)
      = g (Work.Cyl.rho x ^ (3 * α)) (psi x) := by
  by_cases h : Work.Cyl.radial x = 0
  · -- on the symmetry axis: `psi x = π/2` and `theta x = 0`
    have hθ : Work.Cyl.theta x = 0 := by
      rw [Work.Cyl.theta, h, div_zero, Real.arctan_zero]
    rw [psi, h, zero_div, Real.arccos_zero, hθ, abs_zero, hvt.1, hvt.2]
  · -- off the symmetry axis `psi` is literally `|theta|`
    have hpos : 0 < Work.Cyl.radial x :=
      lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm h)
    rw [psi_eq_abs_theta hpos]

end Work.ConstructionInstance
