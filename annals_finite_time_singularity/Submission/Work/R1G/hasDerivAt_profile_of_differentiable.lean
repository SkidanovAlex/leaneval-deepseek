import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.ConstructionInstance.profile_add_z_pz_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-- **The `z`-derivative of the profile of an arbitrary perturbation.**

If each `z`-slice `z' ↦ g z' θ` of the perturbation is differentiable at `z`, then the `z`-slice
`z' ↦ profile p g z' θ` of the profile `F = F_* + g` (oddly extended in `θ`) is differentiable at
`z > 0`: on the branch `θ ≥ 0` it is `F_* + g`, on `θ < 0` it is the negated reflection of the
same.  Hence it satisfies `HasDerivAt` with the value of `deriv` at `z`, which is by definition
`Work.Spaces.pz`. -/
theorem hasDerivAt_profile_of_differentiable {p : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : ∀ z θ : ℝ, DifferentiableAt ℝ (fun z' : ℝ => g z' θ) z) {z θ : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => Work.ConstructionInstance.profile p g z' θ)
      (Work.Spaces.pz (Work.ConstructionInstance.profile p g) z θ) z := by
  have hz1 : (-1 : ℝ) < z := by linarith
  have hslice : DifferentiableAt ℝ
      (fun z' => Work.ConstructionInstance.profile p g z' θ) z := by
    by_cases hθ : 0 ≤ θ
    · have hEq : (fun z' => Work.ConstructionInstance.profile p g z' θ)
          = fun z' => Work.Construction.Fstar p z' θ + g z' θ := by
        funext z'
        exact Work.ConstructionInstance.profile_of_nonneg hθ
      rw [hEq]
      exact ((Work.ConstructionInstance.hasDerivAt_Fstar_z z θ hz1).differentiableAt).add
        (hg z θ)
    · have hEq : (fun z' => Work.ConstructionInstance.profile p g z' θ)
          = fun z' => -(Work.Construction.Fstar p z' (-θ) + g z' (-θ)) := by
        funext z'
        exact Work.ConstructionInstance.profile_of_neg hθ
      rw [hEq]
      exact (((Work.ConstructionInstance.hasDerivAt_Fstar_z z (-θ) hz1).differentiableAt).add
        (hg z (-θ))).neg
  exact hslice.hasDerivAt

end Work.R1G
