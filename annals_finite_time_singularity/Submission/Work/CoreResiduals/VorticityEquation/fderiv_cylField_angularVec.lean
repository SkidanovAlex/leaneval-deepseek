import Mathlib.Analysis.Calculus.FDeriv.Defs
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

/-- `angularVec x = -x₀ e₁ + x₁ e₀` is the linear vector `r e_θ`, written in the standard
basis. -/
private lemma angularVec_eq_smul_basis (x : R3) :
    angularVec x = (-x 1) • basisVec 0 + (x 0) • basisVec 1 := by
  apply ext_coord <;> simp [angularVec, basisVec, FiniteTimeSingularity.e]

/-- The derivative of `cylField ur uz` in the angular direction `angularVec x = r e_θ`.  Since the
field is `u_r(r,x₃) e_r + u_z(r,x₃) e₃` and `r e_θ` is tangent to the circle `r = const`, only the
`r e_r`-factor contributes: the profile factors differentiate to zero along this direction, and
`d(r e_r)[r e_θ] = r e_θ`. -/
theorem fderiv_cylField_angularVec (ur uz : ℝ → ℝ → ℝ) (x : Work.Cyl.R3)
    (hur : Work.Cyl.DiffAt2 ur (Work.Cyl.radial x) (Work.Cyl.axial x))
    (huz : Work.Cyl.DiffAt2 uz (Work.Cyl.radial x) (Work.Cyl.axial x))
    (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ (Work.Cyl.cylField ur uz) x (Work.Cyl.angularVec x)
      = Work.Cyl.redR ur (Work.Cyl.radial x) (Work.Cyl.axial x) • Work.Cyl.angularVec x := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hd := differentiableAt_cylField ur uz x hur huz hr
  rw [angularVec_eq_smul_basis x, map_add, map_smul, map_smul]
  apply ext_coord
  · simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [fderiv_apply_coord (cylField ur uz) x 0 0 hd, fderiv_apply_coord (cylField ur uz) x 1 0 hd,
      pd_cylField_00 ur uz x hur hr, pd_cylField_10 ur uz x hur hr]
    simp only [redR, basisVec_zero, basisVec_one, e0_apply_zero, e1_apply_zero]
    field_simp
    ring
  · simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [fderiv_apply_coord (cylField ur uz) x 0 1 hd, fderiv_apply_coord (cylField ur uz) x 1 1 hd,
      pd_cylField_01 ur uz x hur hr, pd_cylField_11 ur uz x hur hr]
    simp only [redR, basisVec_zero, basisVec_one, e0_apply_one, e1_apply_one]
    field_simp
    ring
  · simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [fderiv_apply_coord (cylField ur uz) x 0 2 hd, fderiv_apply_coord (cylField ur uz) x 1 2 hd,
      pd_cylField_02 ur uz x huz hr, pd_cylField_12 ur uz x huz hr]
    simp only [redR, basisVec_zero, basisVec_one, e0_apply_two, e1_apply_two]
    field_simp
    ring

end Work.CoreResiduals.VorticityEquation
