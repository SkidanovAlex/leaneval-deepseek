import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.FieldDeriv
import Submission.Work.Cyl.Transfer

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The axial derivative of `x ↦ F(ρ(x)^α, θ(x))`: the `e₃` direction

For a two-variable function `F`, a real exponent `α` and a point `x` off the symmetry axis
(`0 < radial x`),

`fderiv ℝ (fun y ↦ F (rho y ^ α) (theta y)) x eZ
   = (sin θ / ρ) · (α ρ^α ∂_R F(ρ^α,θ)) + (cos θ / ρ) · ∂_θ F(ρ^α,θ)`,

with `(ρ, θ) = (rho x, theta x)`.

Geometrically: along the vertical line `x + t e₃` the point `(ρ, θ)` moves as
`(ρ(x₃), θ(x₃))` with `∂_{x₃}ρ = x₃/ρ = sin θ` and `∂_{x₃}θ = radial/ρ² = cos θ/ρ`, and
`e₃` is the coordinate direction `∂_{x₃}`.  The `(r, x₃)`-plane computation is
`Work.Cyl.pdZ_comp_polar`; the present lemma transports it to `ℝ³` along the line
`x + t e₃`, on which `radial` is constant and `axial` increases at unit speed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-! ## The dictionary between `(rho, theta)` on `ℝ³` and `(rhoP, thetaP)` on the half plane -/

private lemma rho_eq_rhoP (y : R3) : rho y = rhoP (radial y) (axial y) := by
  rw [rho, rhoP, radial_sq]

private lemma theta_eq_thetaP (y : R3) : theta y = thetaP (radial y) (axial y) := rfl

/-- On the vertical line through `x` the coordinates `(ρ, θ)` are the plane polar coordinates of
`(radial x, axial x + t)`. -/
private lemma rho_add_smul_eZ (x : R3) (t : ℝ) :
    rho (x + t • eZ) = rhoP (radial x) (axial x + t) := by
  rw [rho_eq_rhoP, radial_add_smul_eZ, axial_add_smul_eZ]

private lemma theta_add_smul_eZ (x : R3) (t : ℝ) :
    theta (x + t • eZ) = thetaP (radial x) (axial x + t) := by
  rw [theta_eq_thetaP, radial_add_smul_eZ, axial_add_smul_eZ]

private lemma rhoP_radial_axial (x : R3) : rhoP (radial x) (axial x) = rho x :=
  (rho_eq_rhoP x).symm

private lemma thetaP_radial_axial (x : R3) : thetaP (radial x) (axial x) = theta x := rfl

/-! ## Differentiability of `ρ` and `θ` off the axis -/

private lemma differentiableAt_rho_of_pos (x : R3) (hr : 0 < radial x) :
    DifferentiableAt ℝ rho x := by
  have hinner : DifferentiableAt ℝ (fun y : R3 => radSq y + axial y ^ 2) x := by
    have hEq : (fun y : R3 => radSq y + axial y ^ 2) =
        fun y : R3 => y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
      funext y; simp [radSq, axial]
    rw [hEq]; fun_prop
  have hpos : 0 < radSq x := by rw [← radial_sq]; positivity
  have hne : (fun y : R3 => radSq y + axial y ^ 2) x ≠ 0 := by
    show radSq x + axial x ^ 2 ≠ 0
    exact ne_of_gt (add_pos_of_pos_of_nonneg hpos (sq_nonneg _))
  exact hinner.sqrt hne

private lemma differentiableAt_theta_of_pos (x : R3) (hr : 0 < radial x) :
    DifferentiableAt ℝ theta x := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hdiv : DifferentiableAt ℝ (fun y : R3 => axial y * (radial y)⁻¹) x :=
    (differentiableAt_axial x).mul ((differentiableAt_radial x hrne).inv hrne)
  exact hdiv.arctan

/-- Off the axis, `y ↦ F (rho y ^ α) (theta y)` is differentiable at `x` when `F` is
differentiable at `(rho x ^ α, theta x)`. -/
private lemma differentiableAt_rhoPow_theta_comp (F : ℝ → ℝ → ℝ) (α : ℝ) (x : R3)
    (hF : DiffAt2 F (rho x ^ α) (theta x)) (hr : 0 < radial x) :
    DifferentiableAt ℝ (fun y : R3 => F (rho y ^ α) (theta y)) x := by
  have hrho_pos : 0 < rho x := lt_of_lt_of_le hr (radial_le_rho x)
  have hrhoPow : DifferentiableAt ℝ (fun y : R3 => rho y ^ α) x :=
    (differentiableAt_rho_of_pos x hr).rpow_const (Or.inl (ne_of_gt hrho_pos))
  have hpair : DifferentiableAt ℝ (fun y : R3 => (rho y ^ α, theta y)) x :=
    hrhoPow.prodMk (differentiableAt_theta_of_pos x hr)
  simpa [Function.comp_def] using hF.comp x hpair

/-! ## The chain rule along a vertical line in the `(r, x₃)` half plane -/

private lemma deriv_rhoP_thetaP_shift (F : ℝ → ℝ → ℝ) (α r z : ℝ) (hr : 0 < r)
    (hF : DiffAt2 F (rhoP r z ^ α) (thetaP r z)) :
    deriv (fun t : ℝ => F (rhoP r (z + t) ^ α) (thetaP r (z + t))) 0 =
      Real.sin (thetaP r z) / rhoP r z *
          (α * rhoP r z ^ α * pdR F (rhoP r z ^ α) (thetaP r z))
        + Real.cos (thetaP r z) / rhoP r z * pdZ F (rhoP r z ^ α) (thetaP r z) := by
  rw [deriv_comp_const_add (fun u : ℝ => F (rhoP r u ^ α) (thetaP r u)) z 0, add_zero]
  rw [show deriv (fun u : ℝ => F (rhoP r u ^ α) (thetaP r u)) z
      = pdZ (fun r' z' => F (rhoP r' z' ^ α) (thetaP r' z')) r z from rfl]
  exact pdZ_comp_polar F α r z hr hF

theorem fderiv_R_theta_eZ (F : ℝ → ℝ → ℝ) (α : ℝ) (x : Work.Cyl.R3)
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rho x ^ α) (Work.Cyl.theta x)) (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ (fun y : Work.Cyl.R3 => F (Work.Cyl.rho y ^ α) (Work.Cyl.theta y)) x Work.Cyl.eZ =
      Real.sin (Work.Cyl.theta x) / Work.Cyl.rho x *
          (α * Work.Cyl.rho x ^ α * Work.Cyl.pdR F (Work.Cyl.rho x ^ α) (Work.Cyl.theta x))
        + Real.cos (Work.Cyl.theta x) / Work.Cyl.rho x *
          Work.Cyl.pdZ F (Work.Cyl.rho x ^ α) (Work.Cyl.theta x) := by
  have hd := differentiableAt_rhoPow_theta_comp F α x hF hr
  rw [fderiv_apply_eq_deriv_line _ _ _ hd]
  have hmain : (fun t : ℝ => F (rho (x + t • eZ) ^ α) (theta (x + t • eZ))) =
      fun t : ℝ => F (rhoP (radial x) (axial x + t) ^ α) (thetaP (radial x) (axial x + t)) := by
    funext t; rw [rho_add_smul_eZ, theta_add_smul_eZ]
  have hF' : DiffAt2 F (rhoP (radial x) (axial x) ^ α) (thetaP (radial x) (axial x)) := by
    rw [rhoP_radial_axial, thetaP_radial_axial]; exact hF
  rw [hmain, deriv_rhoP_thetaP_shift F α (radial x) (axial x) hr hF']
  rw [rhoP_radial_axial, thetaP_radial_axial]

end Work.Cyl
