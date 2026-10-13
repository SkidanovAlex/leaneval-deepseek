import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.R1G.GTest
import Submission.Work.ConstructionInstance.profile_add_z_pz_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-- The `z`-slice of the test perturbation `gTest ε` is differentiable at every point:
`θ ↦ ε·sin(2θ)` is a constant of the slice and `z ↦ z²e^{-z}` is smooth. -/
theorem differentiableAt_gTest_slice (ε θ z : ℝ) :
    DifferentiableAt ℝ (fun z' => gTest ε z' θ) z := by
  have h : HasDerivAt (fun z' : ℝ => ε * gPhi z' * gPsi θ) (ε * gPhi1 z * gPsi θ) z :=
    ((hasDerivAt_gPhi z).const_mul ε).mul_const (gPsi θ)
  have hfun : (fun z' => gTest ε z' θ) = fun z' => ε * gPhi z' * gPsi θ := by
    funext z'; rw [gTest_apply]
  rw [hfun]
  exact h.differentiableAt

/-- **The `z`-derivative of the profile of the test perturbation.**

For `z > 0` the `z`-slice `z' ↦ profile p (gTest ε) z' θ` is differentiable (it is `F_* + g` on the
branch `θ ≥ 0` and the negated reflection on `θ < 0`), so it satisfies `HasDerivAt` with the value
of `deriv` at `z`, which is by definition `Work.Spaces.pz`. -/
theorem gTest_profile_deriv (p : ℝ) (ε : ℝ) :
    ∀ z θ : ℝ, 0 < z →
      HasDerivAt (fun z' => Work.ConstructionInstance.profile p (gTest ε) z' θ)
        (Work.Spaces.pz (Work.ConstructionInstance.profile p (gTest ε)) z θ) z := by
  intro z θ hz
  have hz1 : (-1 : ℝ) < z := by linarith
  have hslice : DifferentiableAt ℝ
      (fun z' => Work.ConstructionInstance.profile p (gTest ε) z' θ) z := by
    by_cases hθ : 0 ≤ θ
    · have hEq : (fun z' => Work.ConstructionInstance.profile p (gTest ε) z' θ)
          = fun z' => Work.Construction.Fstar p z' θ + gTest ε z' θ := by
        funext z'
        exact Work.ConstructionInstance.profile_of_nonneg hθ
      rw [hEq]
      exact ((Work.ConstructionInstance.hasDerivAt_Fstar_z z θ hz1).differentiableAt).add
        (differentiableAt_gTest_slice ε θ z)
    · have hEq : (fun z' => Work.ConstructionInstance.profile p (gTest ε) z' θ)
          = fun z' => -(Work.Construction.Fstar p z' (-θ) + gTest ε z' (-θ)) := by
        funext z'
        exact Work.ConstructionInstance.profile_of_neg hθ
      rw [hEq]
      exact (((Work.ConstructionInstance.hasDerivAt_Fstar_z z (-θ) hz1).differentiableAt).add
        (differentiableAt_gTest_slice ε (-θ) z)).neg
  exact hslice.hasDerivAt

end Work.R1G
