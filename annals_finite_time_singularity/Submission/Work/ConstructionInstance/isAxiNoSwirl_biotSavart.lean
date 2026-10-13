import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.ConstructionInstance.AxiNoSwirlSymm
import Submission.Work.ConstructionInstance.biotSavart_rotLE
import Submission.Work.ConstructionInstance.biotSavart_flip1
import Submission.Work.ConstructionInstance.exists_rotLE_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **The Biot–Savart field of an axisymmetric toroidal (swirl) vorticity is axisymmetric
without swirl.**

The vorticity profile `ω x = f (radial x) (axial x) • e_θ(x)` is equivariant under every rotation
`rotLE φ` about the `x₃`-axis (`omega_rotLE`) and anti-invariant under the reflection
`flip1 : x ↦ (x₀,-x₁,x₃)` (`omega_flip1`).  Both properties pass to the Biot–Savart integral,
because substituting `y ↦ g y` (`g` a linear isometry of `ℝ³`) in the Newtonian-potential
integral turns the integrand into `g` of itself — this is `biotSavart_rotLE` for the rotations
and `biotSavart_flip1` for the reflection.  The two resulting symmetries of `u = biotSavart ω`,
together with the existence of the rotation taking a point of the meridian `x₁ = 0` to any point
off the axis (`exists_rotLE_eq`), give `IsAxiNoSwirl u` (`isAxiNoSwirl_of_rot_flip`). -/
theorem isAxiNoSwirl_biotSavart {ω : Work.ConstructionInstance.R3 → Work.ConstructionInstance.R3}
    {f : ℝ → ℝ → ℝ}
    (hω : ∀ x : Work.ConstructionInstance.R3,
      ω x = f (Work.Cyl.radial x) (Work.Cyl.axial x) • Work.Cyl.eTheta x) :
    Work.Cyl.IsAxiNoSwirl (Work.LWP.biotSavart ω) :=
  isAxiNoSwirl_of_rot_flip (Work.LWP.biotSavart ω)
    (fun φ x => biotSavart_rotLE (fun φ x => omega_rotLE hω φ x) φ x)
    (fun x => biotSavart_flip1 (fun x => omega_flip1 hω x) x)
    exists_rotLE_eq

end Work.ConstructionInstance
