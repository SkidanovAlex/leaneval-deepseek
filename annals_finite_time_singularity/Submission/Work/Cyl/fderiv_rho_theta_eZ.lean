import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.FieldDeriv
import Submission.Work.Cyl.Transfer
import Submission.Work.Cyl.differentiableAt_rho_theta_comp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The axial derivative of `x ↦ F(ρ(x), θ(x))`: the `e₃` direction

For a two-variable function `F` and a point `x` off the symmetry axis (`0 < radial x`),

`fderiv ℝ (fun y ↦ F (rho y) (theta y)) x eZ
   = sin θ · ∂_ρ F(ρ,θ) + (cos θ / ρ) · ∂_θ F(ρ,θ)`,

with `(ρ, θ) = (rho x, theta x)`.  Geometrically: along the vertical line `x + t e₃` the point
`(rho, theta)` moves as `(ρ(x₃), θ(x₃))` with `∂_{x₃}ρ = x₃/ρ = sin θ` and
`∂_{x₃}θ = radial/ρ² = cos θ/ρ`, and `e₃` is the coordinate direction `∂_{x₃}`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-! ## The dictionary between `(rho, theta)` on `ℝ³` and `(rhoP, thetaP)` on the half plane

`rho y = rhoP (radial y) (axial y)` and `theta y = thetaP (radial y) (axial y)`, so on the
vertical line through `x` we have `rho (x + t e₃) = rhoP (radial x) (axial x + t)` and likewise
for `theta`. -/

private lemma rho_eq_rhoP (y : R3) : rho y = rhoP (radial y) (axial y) := by
  rw [rho, rhoP, radial_sq]

private lemma theta_eq_thetaP (y : R3) : theta y = thetaP (radial y) (axial y) := rfl

/-! ## The axial chain rule along a vertical line in the `(r, x₃)` half plane -/

private lemma deriv_rhoP_thetaP_shift (F : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hF : DiffAt2 F (rhoP r z) (thetaP r z)) :
    deriv (fun t : ℝ => F (rhoP r (z + t)) (thetaP r (z + t))) 0 =
      Real.sin (thetaP r z) * pdR F (rhoP r z) (thetaP r z)
        + Real.cos (thetaP r z) / rhoP r z * pdZ F (rhoP r z) (thetaP r z) := by
  rw [deriv_comp_const_add (fun u : ℝ => F (rhoP r u) (thetaP r u)) z 0, add_zero]
  rw [show deriv (fun u : ℝ => F (rhoP r u) (thetaP r u)) z
      = pdZ (fun r' z' => F (rhoP r' z') (thetaP r' z')) r z from rfl]
  exact pdZ_comp_polar_rho F r z hr hF

theorem fderiv_rho_theta_eZ (F : ℝ → ℝ → ℝ) (x : Work.Cyl.R3)
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rho x) (Work.Cyl.theta x)) (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ (fun y : Work.Cyl.R3 => F (Work.Cyl.rho y) (Work.Cyl.theta y)) x Work.Cyl.eZ =
      Real.sin (Work.Cyl.theta x) * Work.Cyl.pdR F (Work.Cyl.rho x) (Work.Cyl.theta x)
        + Real.cos (Work.Cyl.theta x) / Work.Cyl.rho x *
          Work.Cyl.pdZ F (Work.Cyl.rho x) (Work.Cyl.theta x) := by
  have hrho : rho x = rhoP (radial x) (axial x) := rho_eq_rhoP x
  have htheta : theta x = thetaP (radial x) (axial x) := theta_eq_thetaP x
  have hF' : DiffAt2 F (rhoP (radial x) (axial x)) (thetaP (radial x) (axial x)) := by
    rw [← hrho, ← htheta]; exact hF
  rw [fderiv_apply_eq_deriv_line _ _ _ (differentiableAt_rho_theta_comp F x hF hr)]
  have hfun : (fun t : ℝ => F (rho (x + t • eZ)) (theta (x + t • eZ))) =
      fun t : ℝ =>
        F (rhoP (radial x) (axial x + t)) (thetaP (radial x) (axial x + t)) := by
    funext t
    rw [rho_eq_rhoP (x + t • eZ), theta_eq_thetaP (x + t • eZ), radial_add_smul_eZ,
      axial_add_smul_eZ]
  rw [hfun, deriv_rhoP_thetaP_shift F (radial x) (axial x) hr hF']
  rw [← hrho, ← htheta]

end Work.Cyl
