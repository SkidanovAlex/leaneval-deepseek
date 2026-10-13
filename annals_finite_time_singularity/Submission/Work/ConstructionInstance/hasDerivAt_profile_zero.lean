import Mathlib.Analysis.Calculus.Deriv.Add
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

namespace Work.ConstructionInstance

/-- With the zero perturbation `g = 0`, `profile p 0 (·, θ)` is, on each angular branch, a
constant multiple of `Work.FM.Fstar` (via `Work.Construction.Fstar`); hence it is
differentiable in `z` for `z > 0` and its derivative at `z` is `Work.Spaces.pz (profile p 0) z θ`. -/
theorem hasDerivAt_profile_zero {p θ z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' => Work.ConstructionInstance.profile p (fun _ _ => (0 : ℝ)) z' θ)
      (Work.Spaces.pz (Work.ConstructionInstance.profile p fun _ _ => (0 : ℝ)) z θ) z := by
  have hz1 : -1 < z := by linarith
  rcases le_or_gt 0 θ with hθ | hθ
  · -- positive branch: `profile p 0 z' θ = F_*(z',θ)` identically
    have hEq : (fun z' => Work.ConstructionInstance.profile p (fun _ _ => (0 : ℝ)) z' θ)
        = fun z' => Work.Construction.Fstar p z' θ := by
      funext z'; rw [profile_of_nonneg hθ]; simp
    have hval : Work.Spaces.pz (Work.ConstructionInstance.profile p fun _ _ => (0 : ℝ)) z θ
        = Work.Spaces.pz (Work.Construction.Fstar p) z θ := by
      simp only [Work.Spaces.pz, hEq]
    rw [hEq, hval]
    exact hasDerivAt_Fstar_z (p := p) z θ hz1
  · -- negative branch: `profile p 0 z' θ = -(F_*(z',-θ))` identically
    have hEq : (fun z' => Work.ConstructionInstance.profile p (fun _ _ => (0 : ℝ)) z' θ)
        = fun z' => -(Work.Construction.Fstar p z' (-θ)) := by
      funext z'; rw [profile_of_neg (not_le.mpr hθ)]; simp
    have hF := (hasDerivAt_Fstar_z (p := p) z (-θ) hz1).neg
    have hval : Work.Spaces.pz (Work.ConstructionInstance.profile p fun _ _ => (0 : ℝ)) z θ
        = -(Work.Spaces.pz (Work.Construction.Fstar p) z (-θ)) := by
      rw [Work.Spaces.pz, hEq]
      exact hF.deriv
    rw [hEq, hval]
    exact hF

end Work.ConstructionInstance
