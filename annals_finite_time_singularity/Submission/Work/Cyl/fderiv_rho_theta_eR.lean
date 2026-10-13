import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
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
# The radial derivative of `x ↦ F(ρ(x), θ(x))`: the `e_r` direction

For a two-variable function `F` and a point `x` off the symmetry axis (`0 < radial x`),

`fderiv ℝ (fun y ↦ F (rho y) (theta y)) x eR
   = cos θ · ∂_ρ F(ρ,θ) − (sin θ / ρ) · ∂_θ F(ρ,θ)`,

with `(ρ, θ) = (rho x, theta x)`.

Geometrically, moving along the unit radial direction `e_r` increases the planar radius `r` at
unit speed and keeps `x₃` fixed, so the pair `(ρ, θ)` traverses the radial curve
`t ↦ (ρP(r+t, x₃), θP(r+t, x₃))`; the directional derivative is therefore the radial partial
derivative `∂_r` of `(r,z) ↦ F(ρP(r,z), θP(r,z))` evaluated at `(radial x, axial x)`, which is
`Work.Cyl.pdR_comp_polar_rho`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-! ## The dictionary between `(rho, theta)` on ℝ³ and `(rhoP, thetaP)` on the half plane -/

private lemma rho_eq_rhoP_aux (y : R3) : rho y = rhoP (radial y) (axial y) := by
  rw [rho, rhoP, radial_sq]

private lemma theta_eq_thetaP_aux (y : R3) : theta y = thetaP (radial y) (axial y) := rfl

/-! ## Differentiability of `(r,z) ↦ F(ρP(r,z), θP(r,z))` -/

/-- If `F` is differentiable as a function of two variables at `(ρP r z, θP r z)` and `0 < r`,
then so is the composite `(r,z) ↦ F(ρP r z, θP r z)`: the pair `(ρP, θP)` is differentiable
there (`ρP` is a square root of a strictly positive quantity, `θP` is `arctan` of the
differentiable quotient `z/r`, legitimate since `r ≠ 0`). -/
private lemma polar_comp_diffAt2_aux (F : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
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
  have hcomp := hF.comp (r, z) hΦ
  exact hcomp

/-! ## Directional derivatives of the planar radius and the axial coordinate -/

/-- `t ↦ radial (x + t • v)` has derivative `((x₀ v₀ + x₁ v₁))/r` at `0`, i.e. the directional
derivative of `r = √(x₀²+x₁²)` in direction `v`. -/
private lemma hasDerivAt_radial_dir_aux (x v : R3) (hr : 0 < radial x) :
    HasDerivAt (fun t : ℝ => radial (x + t • v)) ((x 0 * v 0 + x 1 * v 1) / radial x) 0 := by
  have h0 : HasDerivAt (fun t : ℝ => x 0 + t * v 0) (v 0) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v 0)).const_add (x 0)
  have h1 : HasDerivAt (fun t : ℝ => x 1 + t * v 1) (v 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v 1)).const_add (x 1)
  have hradsq : HasDerivAt (fun t : ℝ => radSq (x + t • v))
      (2 * (x 0 * v 0) + 2 * (x 1 * v 1)) 0 := by
    have hfun : (fun t : ℝ => radSq (x + t • v)) =
        fun t : ℝ => (x 0 + t * v 0) * (x 0 + t * v 0)
          + (x 1 + t * v 1) * (x 1 + t * v 1) := by
      funext t; simp [radSq, pow_two]
    rw [hfun]
    have hsq : HasDerivAt (fun t : ℝ => (x 0 + t * v 0) * (x 0 + t * v 0)
          + (x 1 + t * v 1) * (x 1 + t * v 1))
        (2 * (x 0 * v 0) + 2 * (x 1 * v 1)) 0 := by
      have h := (h0.mul h0).add (h1.mul h1)
      convert h using 1
      ring
    exact hsq
  have hne : radSq (x + (0:ℝ) • v) ≠ 0 := by
    rw [zero_smul, add_zero]
    rw [← radial_sq]; exact pow_ne_zero 2 (ne_of_gt hr)
  have hmain : (fun t : ℝ => radial (x + t • v)) =
      fun t : ℝ => Real.sqrt (radSq (x + t • v)) := by
    funext t; rw [radial]
  rw [hmain]
  have hder := hradsq.sqrt hne
  have hval : (2 * (x 0 * v 0) + 2 * (x 1 * v 1)) / (2 * Real.sqrt (radSq (x + (0:ℝ) • v)))
      = (x 0 * v 0 + x 1 * v 1) / radial x := by
    rw [zero_smul, add_zero, radial]
    have hpos : 0 < radSq x := by rw [← radial_sq]; positivity
    have hsne : Real.sqrt (radSq x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    field_simp
  rw [hval] at hder
  exact hder

/-- `t ↦ axial (x + t • v)` has derivative `v₂` at `0`. -/
private lemma hasDerivAt_axial_dir_aux (x v : R3) :
    HasDerivAt (fun t : ℝ => axial (x + t • v)) (v 2) 0 := by
  have hfun : (fun t : ℝ => axial (x + t • v)) = fun t : ℝ => x 2 + t * v 2 := by
    funext t; simp [axial]
  rw [hfun]
  simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v 2)).const_add (x 2)

/-! ## The main computation -/

theorem fderiv_rho_theta_eR (F : ℝ → ℝ → ℝ) (x : Work.Cyl.R3)
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rho x) (Work.Cyl.theta x)) (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ (fun y : Work.Cyl.R3 => F (Work.Cyl.rho y) (Work.Cyl.theta y)) x (Work.Cyl.eR x) =
      Real.cos (Work.Cyl.theta x) * Work.Cyl.pdR F (Work.Cyl.rho x) (Work.Cyl.theta x)
        - Real.sin (Work.Cyl.theta x) / Work.Cyl.rho x *
          Work.Cyl.pdZ F (Work.Cyl.rho x) (Work.Cyl.theta x) := by
  have hF' : DiffAt2 F (rhoP (radial x) (axial x)) (thetaP (radial x) (axial x)) := by
    rw [← rho_eq_rhoP_aux, ← theta_eq_thetaP_aux]; exact hF
  have hH : DiffAt2 (fun r' z' => F (rhoP r' z') (thetaP r' z')) (radial x) (axial x) :=
    polar_comp_diffAt2_aux F (radial x) (axial x) hr hF'
  have hG : DifferentiableAt ℝ (fun y : R3 => F (rho y) (theta y)) x :=
    differentiableAt_rho_theta_comp F x hF hr
  -- the pair `(radial, axial)` moves with velocity `(1, 0)` along the line `t ↦ x + t • eR x`
  have hradline : HasDerivAt (fun t : ℝ => radial (x + t • eR x)) 1 0 := by
    have h := hasDerivAt_radial_dir_aux x (eR x) hr
    have hval : (x 0 * (eR x) 0 + x 1 * (eR x) 1) / radial x = 1 := by
      rw [eR_apply_zero, eR_apply_one]
      field_simp
      rw [radial_sq]; rfl
    rw [hval] at h; exact h
  have haxline : HasDerivAt (fun t : ℝ => axial (x + t • eR x)) 0 0 := by
    have h := hasDerivAt_axial_dir_aux x (eR x)
    simpa [eR_apply_two] using h
  have hH0 : DiffAt2 (fun r' z' => F (rhoP r' z') (thetaP r' z'))
      (radial (x + (0:ℝ) • eR x)) (axial (x + (0:ℝ) • eR x)) := by simpa using hH
  have hline : HasDerivAt (fun t : ℝ => F (rho (x + t • eR x)) (theta (x + t • eR x)))
      (pdR (fun r' z' => F (rhoP r' z') (thetaP r' z')) (radial x) (axial x)) 0 := by
    have hc := hasDerivAt_comp_two (fun r' z' => F (rhoP r' z') (thetaP r' z'))
      (fun t : ℝ => radial (x + t • eR x)) (fun t : ℝ => axial (x + t • eR x))
      1 0 0 hH0 hradline haxline
    have heq : (fun t : ℝ => F (rho (x + t • eR x)) (theta (x + t • eR x))) =
        fun t : ℝ => (fun r' z' => F (rhoP r' z') (thetaP r' z'))
          (radial (x + t • eR x)) (axial (x + t • eR x)) := by
      funext t; rw [rho_eq_rhoP_aux (x + t • eR x), theta_eq_thetaP_aux (x + t • eR x)]
    rw [heq]
    simpa using hc
  rw [fderiv_apply_eq_deriv_line _ _ _ hG]
  rw [hline.deriv]
  rw [pdR_comp_polar_rho F (radial x) (axial x) hr hF']
  rw [rho_eq_rhoP_aux x, theta_eq_thetaP_aux x]

end Work.Cyl
