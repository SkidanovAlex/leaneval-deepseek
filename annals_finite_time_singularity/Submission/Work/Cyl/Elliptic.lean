import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Cyl.vorticity_psiField
import Submission.Work.Cyl.div_psiField
import Submission.Work.Cyl.vortTheta_psiField

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The stream-function field: vorticity, divergence and the elliptic reduction

For the stream-function field `psiField ψ` (i.e. `u_r = ∂_z ψ`, `u_z = -ψ/r - ∂_r ψ`):

* `Work.Cyl.vorticity_psiField` : `∇×u = -(Lψ) e_θ`, i.e. `ω^θ = -Lψ` where
  `Lψ = -∂_rrψ - ∂_zzψ - (1/r)∂_rψ + ψ/r²` is `Work.Cyl.cylOp ψ` (paper (3dBSL));
* `Work.Cyl.vortTheta_psiField` : the same identity for `Work.Cyl.vortTheta` on the `(r,x₃)` plane;
* `Work.Cyl.div_psiField` : `div u = 0`.

`Work.Cyl.norm_vorticity_psiField` below records the pointwise norm of the vorticity.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-- The pointwise norm of the vorticity of a stream-function field is `|Lψ|`. -/
theorem norm_vorticity_psiField (ψ : ℝ → ℝ → ℝ) (x : R3)
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (radial x, axial x))
    (hr : 0 < radial x) :
    ‖FiniteTimeSingularity.vorticity (psiField ψ) x‖ =
      |cylOp ψ (radial x) (axial x)| := by
  rw [vorticity_psiField ψ x hψ hr, norm_smul, Real.norm_eq_abs,
    norm_eTheta x (ne_of_gt hr), mul_one]
  exact abs_neg _

/-- The elliptic reduction (paper (3dBSL)) in the form used by the elliptic estimates: the scalar
vorticity of the field is minus the elliptic operator applied to the stream function. -/
theorem vorticityScalar_psiField (ψ : ℝ → ℝ → ℝ) (x : R3)
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (radial x, axial x))
    (hr : 0 < radial x) :
    vortTheta (pdZ ψ) (fun r z => -(ψ r z / r) - pdR ψ r z) (radial x) (axial x)
      = -cylOp ψ (radial x) (axial x) :=
  vortTheta_psiField ψ (radial x) (axial x) hψ (ne_of_gt hr)

end Work.Cyl
