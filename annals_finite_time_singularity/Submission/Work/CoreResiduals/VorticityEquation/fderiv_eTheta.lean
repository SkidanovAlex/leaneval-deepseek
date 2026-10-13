import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.FieldDeriv
import Submission.Work.Cyl.fderiv_radial_apply
import Submission.Work.Cyl.fderiv_angularVec_apply

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Fréchet derivative of the angular unit vector `e_θ`

`e_θ = (1/r) • angularVec` with `r = radial x = √(x₀² + x₁²)` and `angularVec x = (-x₁, x₀, 0)`,
so off the axis (`0 < radial x`) the product rule gives

`fderiv ℝ e_θ x v = -(x₀v₀ + x₁v₁)/r³ • angularVec x + (1/r) • angularVec v`,

the first term being the derivative of the factor `1/r` (whose derivative in direction `v` is
`-(x₀v₀+x₁v₁)/r³`) and the second the derivative of the linear map `angularVec` (which is itself).
-/

namespace Work.CoreResiduals.VorticityEquation

open Work.Cyl

theorem fderiv_eTheta (x v : Work.Cyl.R3) (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ (fun y : Work.Cyl.R3 => Work.Cyl.eTheta y) x v
      = (-(x 0 * v 0 + x 1 * v 1) / (Work.Cyl.radial x) ^ 3) • Work.Cyl.angularVec x
        + ((Work.Cyl.radial x)⁻¹) • Work.Cyl.angularVec v := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  -- `e_θ = (1/r) • angularVec`
  have hfun : eTheta = (fun y : R3 => (radial y)⁻¹) • angularVec := by
    funext y
    show (1 / radial y) • angularVec y = (radial y)⁻¹ • angularVec y
    rw [one_div]
  have hdiffInv : DifferentiableAt ℝ (fun y : R3 => (radial y)⁻¹) x :=
    (differentiableAt_radial x hrne).inv hrne
  have hdiffAng : DifferentiableAt ℝ angularVec x := by
    have h : angularVec = fun y : R3 => (-(y 1)) • e0 + (y 0) • e1 := by
      funext y
      apply ext_coord <;>
        simp [angularVec, e0, e1, FiniteTimeSingularity.e]
    rw [h]; fun_prop
  -- derivative of the radial weight
  have hrad : fderiv ℝ radial x v = (x 0 * v 0 + x 1 * v 1) / radial x :=
    Work.Cyl.fderiv_radial_apply x v hr
  -- derivative of the linear map `angularVec` is `angularVec` itself
  have hang : fderiv ℝ angularVec x v = angularVec v :=
    Work.Cyl.fderiv_angularVec_apply x v
  -- derivative of `y ↦ (radial y)⁻¹`, by the chain rule through `s ↦ s⁻¹`
  have hderivInv : fderiv ℝ (fun y : R3 => (radial y)⁻¹) x v
      = -(x 0 * v 0 + x 1 * v 1) / (radial x) ^ 3 := by
    have hcomp : fderiv ℝ (fun y : R3 => (radial y)⁻¹) x
        = (fderiv ℝ (fun s : ℝ => s⁻¹) (radial x)).comp (fderiv ℝ radial x) := by
      have h := fderiv_comp (𝕜 := ℝ) x (f := radial) (g := fun s : ℝ => s⁻¹)
        (differentiableAt_inv hrne) (differentiableAt_radial x hrne)
      simpa [Function.comp_def] using h
    rw [hcomp, fderiv_inv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul]
    rw [hrad]
    field_simp
  -- product rule
  rw [hfun, fderiv_smul (𝕜 := ℝ) hdiffInv hdiffAng]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, hderivInv, hang]
  abel

end Work.CoreResiduals.VorticityEquation
