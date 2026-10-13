import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.FieldDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.VorticityEquation

open Work.Cyl

/-- The directional derivative of `y ↦ G (radial y) (axial y)` in the direction `v`, for a
two-variable function `G` differentiable at `(radial x, axial x)` and `x` off the symmetry axis.

The pair `(radial, axial)` moves with velocity `(x₀v₀+x₁v₁)/r` and `v₂`, so the derivative is
`∂_r G · (x₀v₀+x₁v₁)/r + ∂_z G · v₂`. -/
theorem fderiv_comp_radial_axial (G : ℝ → ℝ → ℝ) (x v : Work.Cyl.R3)
    (hG : Work.Cyl.DiffAt2 G (Work.Cyl.radial x) (Work.Cyl.axial x))
    (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ (fun y : Work.Cyl.R3 => G (Work.Cyl.radial y) (Work.Cyl.axial y)) x v
      = Work.Cyl.pdR G (Work.Cyl.radial x) (Work.Cyl.axial x)
          * ((x 0 * v 0 + x 1 * v 1) / Work.Cyl.radial x)
        + Work.Cyl.pdZ G (Work.Cyl.radial x) (Work.Cyl.axial x) * v 2 := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  -- differentiability of the composite
  have hGd : DifferentiableAt ℝ (fun y : R3 => G (radial y) (axial y)) x := by
    have hpair : DifferentiableAt ℝ (fun y : R3 => (radial y, axial y)) x :=
      (differentiableAt_radial x hrne).hasFDerivAt.prodMk
        (differentiableAt_axial x).hasFDerivAt |>.differentiableAt
    have h := hG.comp x hpair
    convert h using 1
    funext y; rfl
  -- split `v` in the standard basis
  have hv : v = v 0 • e0 + v 1 • e1 + v 2 • eZ := by
    refine ext_coord ?_ ?_ ?_ <;> simp [e0, e1, eZ, FiniteTimeSingularity.e]
  -- the values of the differential on the three basis vectors
  have h0 : fderiv ℝ (fun y : R3 => G (radial y) (axial y)) x e0
      = pdR G (radial x) (axial x) * (x 0 / radial x) := by
    rw [fderiv_apply_eq_deriv_line _ _ _ hGd]
    exact (hasDerivAt_comp_cyl_e0 G x hG hr).deriv
  have h1 : fderiv ℝ (fun y : R3 => G (radial y) (axial y)) x e1
      = pdR G (radial x) (axial x) * (x 1 / radial x) := by
    rw [fderiv_apply_eq_deriv_line _ _ _ hGd]
    exact (hasDerivAt_comp_cyl_e1 G x hG hr).deriv
  have h2 : fderiv ℝ (fun y : R3 => G (radial y) (axial y)) x eZ
      = pdZ G (radial x) (axial x) := by
    rw [fderiv_apply_eq_deriv_line _ _ _ hGd]
    exact (hasDerivAt_comp_cyl_eZ G x hG hr).deriv
  have hsplit : fderiv ℝ (fun y : R3 => G (radial y) (axial y)) x v
      = fderiv ℝ (fun y : R3 => G (radial y) (axial y)) x (v 0 • e0 + v 1 • e1 + v 2 • eZ) :=
    congrArg (fderiv ℝ (fun y : R3 => G (radial y) (axial y)) x) hv
  rw [hsplit, map_add, map_add, map_smul, map_smul, map_smul, h0, h1, h2,
    smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

end Work.CoreResiduals.VorticityEquation
