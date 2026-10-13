import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
# The radial derivative of `x ↦ F(ρ(x)^α, θ(x))`: the `e_r` direction

For a two-variable function `F`, a point `x` off the symmetry axis (`0 < radial x`) and any real
`α`,

`fderiv ℝ (fun y ↦ F (rho y ^ α) (theta y)) x eR
   = (cos θ / ρ) · (α ρ^α ∂_R F(ρ^α, θ)) − (sin θ / ρ) · ∂_θ F(ρ^α, θ)`,

with `(ρ, θ) = (rho x, theta x)`.

Geometrically, moving along the radial direction `e_r` keeps `x₃` fixed and increases `r` at unit
speed: `rho (x + t e_r) = rhoP (r + t) x₃` and `theta (x + t e_r) = thetaP (r + t) x₃` near
`t = 0`, where `r = radial x`, `x₃ = axial x`.  Hence the directional derivative is exactly the
radial partial derivative `∂_r` of `(r,z) ↦ F (ρP(r,z)^α) (θP(r,z))` at `(r, x₃)`, which is
`Work.Cyl.pdR_comp_polar`.
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

/-! ## The line `t ↦ x + t e_r`

Along the radial direction the axial coordinate is constant and the radial coordinate is `r + t`
(up to the absolute value, which only matters away from `t = 0`). -/

private lemma axial_add_smul_eR (y : R3) (t : ℝ) : axial (y + t • eR y) = axial y := by
  simp [axial, eR]

private theorem radial_add_smul_eR (y : R3) (hy : radial y ≠ 0) (t : ℝ) :
    radial (y + t • eR y) = |radial y + t| := by
  have hx : y 0 ^ 2 + y 1 ^ 2 = radial y ^ 2 := (radial_sq y).symm
  have h0 : (y + t • eR y) 0 = y 0 * (1 + t / radial y) := by
    rw [show (y + t • eR y) 0 = y 0 + t * (y 0 / radial y) from by
      simp [eR, div_eq_inv_mul]]
    ring
  have h1 : (y + t • eR y) 1 = y 1 * (1 + t / radial y) := by
    rw [show (y + t • eR y) 1 = y 1 + t * (y 1 / radial y) from by
      simp [eR, div_eq_inv_mul]]
    ring
  have key : radSq (y + t • eR y) = (radial y + t) ^ 2 := by
    rw [radSq, h0, h1]
    have hfac : (y 0 * (1 + t / radial y)) ^ 2 + (y 1 * (1 + t / radial y)) ^ 2
        = (y 0 ^ 2 + y 1 ^ 2) * (1 + t / radial y) ^ 2 := by ring
    rw [hfac, hx]
    field_simp
  rw [radial, key, Real.sqrt_sq_eq_abs]

private theorem hasDerivAt_radial_line_eR (y : R3) (hy : 0 < radial y) :
    HasDerivAt (fun t : ℝ => radial (y + t • eR y)) 1 0 := by
  have hbase : HasDerivAt (fun t : ℝ => radial y + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (radial y)
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds (show -radial y < (0 : ℝ) by linarith)] with t ht
  rw [Set.mem_Ioi] at ht
  rw [radial_add_smul_eR y (ne_of_gt hy) t, abs_of_pos (by linarith)]

/-! ## Differentiability of `rho` and `theta` off the axis -/

private theorem differentiableAt_rho_of_pos (y : R3) (hy : 0 < radial y) :
    DifferentiableAt ℝ rho y := by
  have h1 : DifferentiableAt ℝ (fun z : R3 => radSq z + axial z ^ 2) y := by
    have hfun : (fun z : R3 => radSq z + axial z ^ 2) =
        fun z : R3 => z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
      funext z; simp [radSq, axial]
    rw [hfun]
    fun_prop
  have h2 : (fun z : R3 => radSq z + axial z ^ 2) y ≠ 0 := by
    have hpos : 0 < radSq y + axial y ^ 2 := by
      have h0 : 0 < radial y ^ 2 := pow_pos hy 2
      rw [radial_sq y] at h0
      linarith [sq_nonneg (axial y)]
    exact ne_of_gt hpos
  exact h1.sqrt h2

private theorem differentiableAt_theta_of_pos (y : R3) (hy : 0 < radial y) :
    DifferentiableAt ℝ theta y := by
  have hyne : radial y ≠ 0 := ne_of_gt hy
  have hth : theta = fun z : R3 => Real.arctan (axial z * (radial z)⁻¹) := by
    funext z; rw [theta, div_eq_mul_inv]
  rw [hth]
  apply DifferentiableAt.arctan
  exact (differentiableAt_axial y).mul
    ((differentiableAt_radial y hyne).inv (by simpa using hyne))

/-! ## The main computation -/

theorem fderiv_R_theta_eR (F : ℝ → ℝ → ℝ) (α : ℝ) (x : Work.Cyl.R3)
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rho x ^ α) (Work.Cyl.theta x)) (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ (fun y : Work.Cyl.R3 => F (Work.Cyl.rho y ^ α) (Work.Cyl.theta y)) x (Work.Cyl.eR x) =
      Real.cos (Work.Cyl.theta x) / Work.Cyl.rho x *
          (α * Work.Cyl.rho x ^ α * Work.Cyl.pdR F (Work.Cyl.rho x ^ α) (Work.Cyl.theta x))
        - Real.sin (Work.Cyl.theta x) / Work.Cyl.rho x *
          Work.Cyl.pdZ F (Work.Cyl.rho x ^ α) (Work.Cyl.theta x) := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hrho_ne : rho x ≠ 0 := ne_of_gt (lt_of_lt_of_le hr (radial_le_rho x))
  -- Differentiability of the composite `y ↦ F (rho y ^ α) (theta y)` at `x`.
  have hpair : DifferentiableAt ℝ (fun y : R3 => (rho y ^ α, theta y)) x :=
    ((differentiableAt_rho_of_pos x hr).rpow_const (Or.inl hrho_ne)).prodMk
      (differentiableAt_theta_of_pos x hr)
  have hgdiff : DifferentiableAt ℝ (fun y : R3 => F (rho y ^ α) (theta y)) x := by
    have h := hF.comp x hpair
    convert h using 1
    funext y; rfl
  rw [fderiv_apply_eq_deriv_line _ _ _ hgdiff]
  -- The `(r,z)` expression `F''` of the composite is differentiable at `(r, x₃)`.
  have hF'' : DiffAt2 (fun r z => F (rhoP r z ^ α) (thetaP r z)) (radial x) (axial x) := by
    have hρ : DifferentiableAt ℝ (fun p : ℝ × ℝ => rhoP p.1 p.2 ^ α) (radial x, axial x) := by
      have hρ0 : DifferentiableAt ℝ (fun p : ℝ × ℝ => rhoP p.1 p.2) (radial x, axial x) := by
        have h : (fun p : ℝ × ℝ => rhoP p.1 p.2) = fun p => Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := by
          funext p; rw [rhoP]
        rw [h]
        apply DifferentiableAt.sqrt
        · fun_prop
        · exact ne_of_gt (by positivity)
      exact hρ0.rpow_const (Or.inl (ne_of_gt (rhoP_pos hr (axial x))))
    have hθ : DifferentiableAt ℝ (fun p : ℝ × ℝ => thetaP p.1 p.2) (radial x, axial x) := by
      have h : (fun p : ℝ × ℝ => thetaP p.1 p.2) = fun p => Real.arctan (p.2 * (p.1)⁻¹) := by
        funext p; rw [thetaP, div_eq_mul_inv]
      rw [h]
      apply DifferentiableAt.arctan
      have h1 : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.2) (radial x, axial x) := by fun_prop
      have h2 : DifferentiableAt ℝ (fun p : ℝ × ℝ => (p.1)⁻¹) (radial x, axial x) :=
        (by fun_prop : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1) (radial x, axial x)).inv
          (by simpa using hrne)
      exact h1.mul h2
    have hp : DifferentiableAt ℝ (fun p : ℝ × ℝ => (rhoP p.1 p.2 ^ α, thetaP p.1 p.2))
        (radial x, axial x) := hρ.prodMk hθ
    have hF' := hF
    rw [rho_eq_rhoP x, theta_eq_thetaP x] at hF'
    exact hF'.comp (radial x, axial x) hp
  -- Along `t ↦ x + t e_r` the composite is `t ↦ F'' (radial x + t) (axial x)` (near `t = 0`),
  -- so its derivative at `0` is the radial partial derivative `∂_r F''`.
  have hderiv : HasDerivAt (fun t : ℝ => F (rho (x + t • eR x) ^ α) (theta (x + t • eR x)))
      (pdR (fun r z => F (rhoP r z ^ α) (thetaP r z)) (radial x) (axial x)) 0 := by
    set R : ℝ → ℝ := fun t => radial (x + t • eR x) with hRdef
    set Z : ℝ → ℝ := fun t => axial (x + t • eR x) with hZdef
    have hR : HasDerivAt R 1 0 := by
      rw [hRdef]; exact hasDerivAt_radial_line_eR x hr
    have hZ : HasDerivAt Z 0 0 := by
      rw [hZdef]
      have h : (fun t : ℝ => axial (x + t • eR x)) = fun _ => axial x := by
        funext t; rw [axial_add_smul_eR x t]
      rw [h]; exact hasDerivAt_const (0 : ℝ) (axial x)
    have hR0 : R 0 = radial x := by
      rw [hRdef]
      show radial (x + 0 • eR x) = radial x
      rw [radial_add_smul_eR x hrne 0, add_zero, abs_of_pos hr]
    have hZ0 : Z 0 = axial x := by
      rw [hZdef]; exact axial_add_smul_eR x 0
    have hF''0 : DiffAt2 (fun r z => F (rhoP r z ^ α) (thetaP r z)) (R 0) (Z 0) := by
      rw [hR0, hZ0]; exact hF''
    have hcomp := hasDerivAt_comp_two (fun r z => F (rhoP r z ^ α) (thetaP r z)) R Z 1 0 0
      hF''0 hR hZ
    have hval : pdR (fun r z => F (rhoP r z ^ α) (thetaP r z)) (R 0) (Z 0) * 1
        + pdZ (fun r z => F (rhoP r z ^ α) (thetaP r z)) (R 0) (Z 0) * 0
        = pdR (fun r z => F (rhoP r z ^ α) (thetaP r z)) (radial x) (axial x) := by
      rw [hR0, hZ0]; ring
    rw [hval] at hcomp
    have hfun : (fun t : ℝ => F (rho (x + t • eR x) ^ α) (theta (x + t • eR x)))
        = fun t : ℝ => F (rhoP (R t) (Z t) ^ α) (thetaP (R t) (Z t)) := by
      funext t
      simp only [hRdef, hZdef]
      rw [rho_eq_rhoP (x + t • eR x), theta_eq_thetaP (x + t • eR x)]
    rw [← hfun] at hcomp
    exact hcomp
  rw [hderiv.deriv]
  -- Evaluate the radial partial derivative of `F''` with the transfer lemma.
  have hFpt : DiffAt2 F (rhoP (radial x) (axial x) ^ α) (thetaP (radial x) (axial x)) := by
    rw [← rho_eq_rhoP x, ← theta_eq_thetaP x]; exact hF
  rw [pdR_comp_polar F α (radial x) (axial x) hr hFpt]
  rw [← rho_eq_rhoP x, ← theta_eq_thetaP x]

end Work.Cyl
