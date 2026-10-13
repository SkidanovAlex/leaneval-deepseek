import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.Cyl.fderiv_rho_theta_eR

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular derivative of `x ↦ F(ρ(x), θ(x))`: the `e_θ` direction

For a two-variable function `F` and a point `x` off the symmetry axis (`0 < radial x`),

`fderiv ℝ (fun y ↦ F (rho y) (theta y)) x (eTheta x) = 0`.

Geometrically: `e_θ` is the unit vector of the rotation about the `x₃`-axis, so to first order
moving along `e_θ` changes neither the distance `r` to the axis nor the axial coordinate `x₃`.
Since `ρ = √(r² + x₃²)` and `θ = arctan(x₃/r)` are functions of `(r, x₃)` alone, both are
stationary in the `e_θ` direction; the derivative of any function of `(ρ, θ)` therefore
vanishes there.

Formally, the argument is the same as in the sibling `Work.Cyl.fderiv_rho_theta_eR` and
`Work.Cyl.fderiv_rho_theta_eZ`: rewrite `F (rho ·) (theta ·)` on the line `t ↦ x + t • eTheta x`
as the composite `H (radial ·) (axial ·)` with `H r' z' = F (rhoP r' z') (thetaP r' z')`,
observe that along this particular line `radial` has velocity `0` at `t = 0`
(`radial (x + t • eTheta x) = √(radial x ^ 2 + t ^ 2)`) and `axial` is constant, and apply the
two-variable chain rule.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix

namespace Work.FTS.FireFix.Clauses

open Work.Cyl

/-! ## The dictionary between `(rho, theta)` on `ℝ³` and `(rhoP, thetaP)` on the half plane -/

private lemma rho_eq_rhoP' (y : R3) : rho y = rhoP (radial y) (axial y) := by
  rw [rho, rhoP, radial_sq]

private lemma theta_eq_thetaP' (y : R3) : theta y = thetaP (radial y) (axial y) := rfl

/-- If `F` is differentiable as a function of two variables at `(ρ(r,z), θ(r,z))` and `0 < r`,
then so is the composite `(r',z') ↦ F (ρ(r',z')) (θ(r',z'))`: the pair `(ρ, θ)` is differentiable
there (`ρ` is a square root of a strictly positive quantity, `θ` is `arctan` of the
differentiable quotient `z'/r'`, legitimate since `r' = r ≠ 0`).  This is the same
differentiability input as in `Work.Cyl.pdR_comp_polar_rho`. -/
private lemma polar_comp_diffAt2 (F : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hF : DiffAt2 F (rhoP r z) (thetaP r z)) :
    DiffAt2 (fun r' z' => F (rhoP r' z') (thetaP r' z')) r z := by
  have hρ : DifferentiableAt ℝ (fun p : ℝ × ℝ => rhoP p.1 p.2) (r, z) := by
    have h : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (r, z) := by fun_prop
    have hne : (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (r, z) ≠ 0 := by
      simp only; positivity
    simpa [rhoP] using h.sqrt hne
  have hθ : DifferentiableAt ℝ (fun p : ℝ × ℝ => thetaP p.1 p.2) (r, z) := by
    have hinv : DifferentiableAt ℝ (fun p : ℝ × ℝ => (p.1)⁻¹) (r, z) :=
      differentiableAt_fst.inv (by simpa using hr.ne')
    have h : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.2 * (p.1)⁻¹) (r, z) :=
      differentiableAt_snd.mul hinv
    simpa [thetaP, div_eq_mul_inv] using h.arctan
  have hΦ : DifferentiableAt ℝ (fun p : ℝ × ℝ => (rhoP p.1 p.2, thetaP p.1 p.2)) (r, z) :=
    hρ.prodMk hθ
  exact hF.comp (r, z) hΦ

/-! ## The line `t ↦ x + t • e_θ` and the polar coordinates on it -/

/-- Along the line in direction `e_θ` the distance to the axis moves as `t ↦ √(r² + t²)`: the
`e_θ` field is the infinitesimal generator of the rotation about the axis, which preserves `r`
to first order, so the quadratic `radSq` picks up a `t²` term. -/
private lemma radSq_add_smul_eTheta (x : R3) (hr : radial x ≠ 0) (t : ℝ) :
    radSq (x + t • eTheta x) = radial x ^ 2 + t ^ 2 := by
  have hs : radial x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by rw [radial_sq]; rfl
  have h0 : (x + t • eTheta x) 0 = x 0 - t * x 1 / radial x := by
    simp [div_eq_mul_inv]; ring
  have h1 : (x + t • eTheta x) 1 = x 1 + t * x 0 / radial x := by
    simp [div_eq_mul_inv]; ring
  change (x + t • eTheta x) 0 ^ 2 + (x + t • eTheta x) 1 ^ 2 = radial x ^ 2 + t ^ 2
  rw [h0, h1]
  field_simp
  nlinarith [hs]

/-- `ρ` is constant to first order along the `e_θ` line: `radial (x + t • eTheta x) =
√(radial x ^ 2 + t ^ 2)`. -/
private lemma radial_add_smul_eTheta (x : R3) (hr : radial x ≠ 0) (t : ℝ) :
    radial (x + t • eTheta x) = Real.sqrt (radial x ^ 2 + t ^ 2) := by
  rw [radial, radSq_add_smul_eTheta x hr t]

/-- The axial coordinate is exactly constant along the `e_θ` line (`e_θ` has no `x₃` component). -/
private lemma axial_add_smul_eTheta (x : R3) (t : ℝ) : axial (x + t • eTheta x) = axial x := by
  simp [axial]

/-- The derivative of the distance to the axis along the `e_θ` line vanishes at `t = 0`. -/
private lemma hasDerivAt_radial_line_eTheta (x : R3) (hr : 0 < radial x) :
    HasDerivAt (fun t : ℝ => radial (x + t • eTheta x)) 0 0 := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  rw [show (fun t : ℝ => radial (x + t • eTheta x)) =
      fun t : ℝ => Real.sqrt (radial x ^ 2 + t ^ 2) from
    funext fun t => radial_add_smul_eTheta x hrne t]
  have hinner : HasDerivAt (fun t : ℝ => radial x ^ 2 + t ^ 2) 0 0 := by
    have h : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by simpa using hasDerivAt_pow 2 (0 : ℝ)
    simpa using h.const_add (radial x ^ 2)
  have hne : radial x ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by simpa using pow_ne_zero 2 hrne
  simpa using hinner.sqrt hne

/-- The derivative of the axial coordinate along the `e_θ` line vanishes at `t = 0`. -/
private lemma hasDerivAt_axial_line_eTheta (x : R3) :
    HasDerivAt (fun t : ℝ => axial (x + t • eTheta x)) 0 0 := by
  have h : (fun t : ℝ => axial (x + t • eTheta x)) = fun _ => axial x := by
    funext t; rw [axial_add_smul_eTheta]
  rw [h]
  exact hasDerivAt_const (0 : ℝ) (axial x)

/-! ## The main computation -/

theorem fderiv_rho_theta_eTheta (F : ℝ → ℝ → ℝ) (x : EuclideanSpace ℝ (Fin 3))
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rho x) (Work.Cyl.theta x)) (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => F (Work.Cyl.rho y) (Work.Cyl.theta y)) x
      (Work.Cyl.eTheta x) = 0 := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  -- `F` is differentiable at the polar coordinates of `x`
  have hF' : DiffAt2 F (rhoP (radial x) (axial x)) (thetaP (radial x) (axial x)) := by
    rw [← rho_eq_rhoP' x, ← theta_eq_thetaP' x]; exact hF
  have hH : DiffAt2 (fun r' z' => F (rhoP r' z') (thetaP r' z')) (radial x) (axial x) :=
    polar_comp_diffAt2 F (radial x) (axial x) hr hF'
  -- the polar coordinates of the shifted point move with velocity `(0, 0)`
  have hline : HasDerivAt (fun t : ℝ => (fun r' z' => F (rhoP r' z') (thetaP r' z'))
      (radial (x + t • eTheta x)) (axial (x + t • eTheta x))) 0 0 := by
    have hH0 : DiffAt2 (fun r' z' => F (rhoP r' z') (thetaP r' z'))
        (radial (x + (0 : ℝ) • eTheta x)) (axial (x + (0 : ℝ) • eTheta x)) := by
      simpa using hH
    have h := hasDerivAt_comp_two (fun r' z' => F (rhoP r' z') (thetaP r' z'))
      (fun t : ℝ => radial (x + t • eTheta x)) (fun t : ℝ => axial (x + t • eTheta x))
      0 0 0 hH0 (hasDerivAt_radial_line_eTheta x hr) (hasDerivAt_axial_line_eTheta x)
    simpa using h
  -- rewrite the `fderiv` as a one-dimensional derivative along the `e_θ` line
  rw [fderiv_apply_eq_deriv_line _ _ _ (differentiableAt_rho_theta_comp F x hF hr)]
  have hfun : (fun t : ℝ => F (rho (x + t • eTheta x)) (theta (x + t • eTheta x))) =
      fun t : ℝ => (fun r' z' => F (rhoP r' z') (thetaP r' z'))
        (radial (x + t • eTheta x)) (axial (x + t • eTheta x)) := by
    funext t
    rw [rho_eq_rhoP' (x + t • eTheta x), theta_eq_thetaP' (x + t • eTheta x)]
  rw [hfun, hline.deriv]

end Work.FTS.FireFix.Clauses
