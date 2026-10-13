import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

open FiniteTimeSingularity
open Work.Cyl

/-!
# `div (omegaS p g) = 0` off the symmetry axis

The self-similar vorticity `omegaS p g x = F(ρ(x)^p, θ(x)) • e_θ(x)` is an axisymmetric `e_θ`-field
with no swirl.  Such a field is divergence free away from the axis `r = 0`: its only nonvanishing
component is tangential, and the scalar prefactor is invariant under the rotation flow whose
generator is `e_θ`.

The proof below is the standard decomposition

`div (F • e_θ) x = F x · div e_θ x + (fderiv F x) (e_θ x)`

together with the two facts `div e_θ = 0` and `(fderiv F x) (e_θ x) = 0` (the latter a consequence
of `ρ` and `θ` having vanishing directional derivative along `e_θ`).
-/

/-! ## A helper: the derivative of an even function at `0` -/

/-- The derivative at `0` of a function that is even vanishes. -/
theorem deriv_zero_of_even {f : ℝ → ℝ} (he : ∀ t, f (-t) = f t) : deriv f 0 = 0 := by
  have h := deriv_comp_neg f 0
  simp only [neg_zero] at h
  have hev : (fun t : ℝ => f (-t)) = f := funext he
  rw [hev] at h
  linarith

/-! ## The product rule for the divergence -/

/-- **Divergence of a scalar multiple of a vector field**:
`div (F • v) x = F x · div v x + (fderiv F x) (v x)`.

This is the product rule for the trace of the Jacobian: `fderiv (F • v) x = F x • fderiv v x +
(fderiv F x).smulRight (v x)` and `trace ((fderiv F x).smulRight (v x)) = (fderiv F x) (v x)`. -/
theorem div_smul_eq (F : R3 → ℝ) (v : R3 → R3) (x : R3)
    (hF : DifferentiableAt ℝ F x) (hv : DifferentiableAt ℝ v x) :
    FiniteTimeSingularity.div (F • v) x
      = F x * FiniteTimeSingularity.div v x + fderiv ℝ F x (v x) := by
  have hsmul := fderiv_smul (𝕜 := ℝ) hF hv
  rw [FiniteTimeSingularity.div, FiniteTimeSingularity.div, hsmul]
  rw [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.coe_smulRight]
  rw [map_add, map_smul, LinearMap.trace_smulRight, ContinuousLinearMap.coe_coe]
  ring

/-! ## The line `t ↦ x + t • e_θ` -/

/-- Along `t ↦ x + t • e_θ(x)` the squared planar radius grows as `radSq x + t²`. -/
theorem radSq_add_smul_eTheta (x : R3) (hr : 0 < radial x) (t : ℝ) :
    radSq (x + t • eTheta x) = radSq x + t ^ 2 := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hx2 : x 0 ^ 2 + x 1 ^ 2 = radial x ^ 2 := (radial_sq x).symm
  rw [radSq, radSq]
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    eTheta_apply_zero, eTheta_apply_one]
  field_simp
  nlinarith [hx2]

/-- Along `t ↦ x + t • e_θ(x)` the axial coordinate is constant. -/
theorem axial_add_smul_eTheta (x : R3) (t : ℝ) : axial (x + t • eTheta x) = axial x := by
  simp only [axial, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    eTheta_apply_two, mul_zero, add_zero]

/-- Along `t ↦ x + t • e_θ(x)` the planar radius is `√(radSq x + t²)`. -/
theorem radial_add_smul_eTheta (x : R3) (hr : 0 < radial x) (t : ℝ) :
    radial (x + t • eTheta x) = Real.sqrt (radSq x + t ^ 2) := by
  rw [radial, radSq_add_smul_eTheta x hr t]

/-- Along `t ↦ x + t • e_θ(x)` the three-dimensional radius is `√(rho x ² + t²)`. -/
theorem rho_add_smul_eTheta (x : R3) (hr : 0 < radial x) (t : ℝ) :
    rho (x + t • eTheta x) = Real.sqrt (rho x ^ 2 + t ^ 2) := by
  rw [rho, rho_sq]
  rw [radSq_add_smul_eTheta x hr t, axial_add_smul_eTheta x t]
  ring_nf

/-- Along `t ↦ x + t • e_θ(x)` the angle is `arctan (x₃ / √(radSq x + t²))`. -/
theorem theta_add_smul_eTheta (x : R3) (hr : 0 < radial x) (t : ℝ) :
    theta (x + t • eTheta x) = Real.arctan (axial x / Real.sqrt (radSq x + t ^ 2)) := by
  rw [theta, radial_add_smul_eTheta x hr t, axial_add_smul_eTheta x t]

/-! ## The vanishing directional derivatives along `e_θ` -/

/-- `ρ` has vanishing directional derivative along `e_θ`. -/
theorem fderiv_rho_eTheta (x : R3) (hr : 0 < radial x) :
    fderiv ℝ rho x (eTheta x) = 0 := by
  rw [fderiv_apply_eq_deriv_line rho x (eTheta x) (differentiableAt_rho_of_radial_pos x hr)]
  have hfun : (fun t : ℝ => rho (x + t • eTheta x)) = fun t => Real.sqrt (rho x ^ 2 + t ^ 2) :=
    funext (rho_add_smul_eTheta x hr)
  rw [hfun]
  exact deriv_zero_of_even (fun t => by rw [neg_sq])

/-- `θ` has vanishing directional derivative along `e_θ`. -/
theorem fderiv_theta_eTheta (x : R3) (hr : 0 < radial x) :
    fderiv ℝ theta x (eTheta x) = 0 := by
  rw [fderiv_apply_eq_deriv_line theta x (eTheta x)
    (differentiableAt_theta_of_radial_ne x (ne_of_gt hr))]
  have hfun : (fun t : ℝ => theta (x + t • eTheta x)) =
      fun t => Real.arctan (axial x / Real.sqrt (radSq x + t ^ 2)) :=
    funext (theta_add_smul_eTheta x hr)
  rw [hfun]
  exact deriv_zero_of_even (fun t => by rw [neg_sq])

/-- `ρ^α` has vanishing directional derivative along `e_θ`. -/
theorem fderiv_Rpow_eTheta (x : R3) (hr : 0 < radial x) (α : ℝ) :
    fderiv ℝ (fun y => rho y ^ α) x (eTheta x) = 0 := by
  have hrho_pos : 0 < rho x := lt_of_lt_of_le hr (radial_le_rho x)
  rw [fderiv_apply_eq_deriv_line (fun y => rho y ^ α) x (eTheta x)
    ((differentiableAt_rho_of_radial_pos x hr).rpow_const (Or.inl (ne_of_gt hrho_pos)))]
  have hfun : (fun t : ℝ => rho (x + t • eTheta x) ^ α) =
      fun t => (Real.sqrt (rho x ^ 2 + t ^ 2)) ^ α :=
    funext (fun t => by rw [rho_add_smul_eTheta x hr t])
  rw [hfun]
  exact deriv_zero_of_even (fun t => by rw [neg_sq])

/-- `1/radial` has vanishing directional derivative along `e_θ`. -/
theorem fderiv_radialInv_eTheta (x : R3) (hr : 0 < radial x) :
    fderiv ℝ (fun y => (radial y)⁻¹) x (eTheta x) = 0 := by
  rw [fderiv_apply_eq_deriv_line (fun y => (radial y)⁻¹) x (eTheta x)
    ((differentiableAt_radial x (ne_of_gt hr)).inv (ne_of_gt hr))]
  have hfun : (fun t : ℝ => (radial (x + t • eTheta x))⁻¹) =
      fun t => (Real.sqrt (radSq x + t ^ 2))⁻¹ :=
    funext (fun t => by rw [radial_add_smul_eTheta x hr t])
  rw [hfun]
  exact deriv_zero_of_even (fun t => by rw [neg_sq])

/-- `e_θ = radial • e_θ / radial`, so the same vanishing holds in the direction `angularVec = r e_θ`. -/
theorem fderiv_radialInv_angularVec (x : R3) (hr : 0 < radial x) :
    fderiv ℝ (fun y => (radial y)⁻¹) x (angularVec x) = 0 := by
  have h : angularVec x = radial x • eTheta x := by
    rw [eTheta, smul_smul, one_div, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  rw [h, map_smul, fderiv_radialInv_eTheta x hr, smul_zero]

/-! ## Differentiability of the profile composite and the vorticity direction -/

/-- `y ↦ F (ρ y ^ α) (θ y)` is differentiable at `x` when `F` is differentiable at `(ρ x ^ α, θ x)`
and `0 < radial x`. -/
theorem differentiableAt_rhoPow_theta_comp (F : ℝ → ℝ → ℝ) (α : ℝ) (x : R3)
    (hF : DiffAt2 F (rho x ^ α) (theta x)) (hr : 0 < radial x) :
    DifferentiableAt ℝ (fun y : R3 => F (rho y ^ α) (theta y)) x := by
  have hrho_pos : 0 < rho x := lt_of_lt_of_le hr (radial_le_rho x)
  have hrho : DifferentiableAt ℝ (fun y : R3 => rho y ^ α) x :=
    (differentiableAt_rho_of_radial_pos x hr).rpow_const (Or.inl (ne_of_gt hrho_pos))
  have htheta : DifferentiableAt ℝ theta x := differentiableAt_theta_of_radial_ne x (ne_of_gt hr)
  have hpair : DifferentiableAt ℝ (fun y : R3 => (rho y ^ α, theta y)) x :=
    hrho.prodMk htheta
  simpa [Function.comp_def, DiffAt2] using hF.comp x hpair

/-- `e_θ` is differentiable off the axis. -/
theorem differentiableAt_eTheta (x : R3) (hr : 0 < radial x) : DifferentiableAt ℝ eTheta x := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hinv : DifferentiableAt ℝ (fun y => (radial y)⁻¹) x :=
    (differentiableAt_radial x hrne).inv hrne
  have hvec : DifferentiableAt ℝ angularVec x := by
    have h : angularVec = fun y : R3 => (-y 1) • e0 + (y 0) • e1 := by
      funext y
      apply ext_coord <;>
        simp [angularVec, e0, e1, FiniteTimeSingularity.e]
    rw [h]; fun_prop
  have hfun : eTheta = (fun y => (radial y)⁻¹) • angularVec := by
    funext y
    show (1 / radial y) • angularVec y = (radial y)⁻¹ • angularVec y
    rw [one_div]
  rw [hfun]
  exact hinv.smul hvec

/-- `e_θ` is divergence free off the axis. -/
theorem div_eTheta (x : R3) (hr : 0 < radial x) : FiniteTimeSingularity.div eTheta x = 0 := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hinv : DifferentiableAt ℝ (fun y => (radial y)⁻¹) x :=
    (differentiableAt_radial x hrne).inv hrne
  have hvec : DifferentiableAt ℝ angularVec x := by
    have h : angularVec = fun y : R3 => (-y 1) • e0 + (y 0) • e1 := by
      funext y
      apply ext_coord <;>
        simp [angularVec, e0, e1, FiniteTimeSingularity.e]
    rw [h]; fun_prop
  have hdivAng : FiniteTimeSingularity.div angularVec x = 0 := by
    rw [div_eq_sum_partials angularVec x hvec, Fin.sum_univ_three]
    have h0 : (fun t : ℝ => (angularVec (x + t • basisVec 0)).ofLp 0) = fun _ => - x 1 := by
      funext t; rw [basisVec_zero, angularVec_apply_zero, add_smul_e0_apply_one]
    have h1 : (fun t : ℝ => (angularVec (x + t • basisVec 1)).ofLp 1) = fun _ => x 0 := by
      funext t; rw [basisVec_one, angularVec_apply_one, add_smul_e1_apply_zero]
    have h2 : (fun t : ℝ => (angularVec (x + t • basisVec 2)).ofLp 2) = fun _ => (0:ℝ) := by
      funext t; rw [angularVec_apply_two]
    rw [h0, h1, h2]
    simp
  have hfun : eTheta = (fun y => (radial y)⁻¹) • angularVec := by
    funext y
    show (1 / radial y) • angularVec y = (radial y)⁻¹ • angularVec y
    rw [one_div]
  rw [hfun, div_smul_eq (fun y => (radial y)⁻¹) angularVec x hinv hvec, hdivAng,
    fderiv_radialInv_angularVec x hr]
  ring

/-! ## The directional derivative of the profile along `e_θ` -/

/-- `(fderiv (F (ρ^α, θ))) (e_θ) = 0`: the profile of an axisymmetric field has vanishing
directional derivative along the angular direction. -/
theorem fderiv_R_theta_eTheta (F : ℝ → ℝ → ℝ) (α : ℝ) (x : R3)
    (hF : DiffAt2 F (rho x ^ α) (theta x)) (hr : 0 < radial x) :
    fderiv ℝ (fun y : R3 => F (rho y ^ α) (theta y)) x (eTheta x) = 0 := by
  have hrho_pos : 0 < rho x := lt_of_lt_of_le hr (radial_le_rho x)
  have hrho : DifferentiableAt ℝ (fun y : R3 => rho y ^ α) x :=
    (differentiableAt_rho_of_radial_pos x hr).rpow_const (Or.inl (ne_of_gt hrho_pos))
  have htheta : DifferentiableAt ℝ theta x := differentiableAt_theta_of_radial_ne x (ne_of_gt hr)
  have hG : DifferentiableAt ℝ (fun y : R3 => (rho y ^ α, theta y)) x := hrho.prodMk htheta
  have hFd : DifferentiableAt ℝ (Function.uncurry F) (rho x ^ α, theta x) := hF
  have hfun : (fun y : R3 => F (rho y ^ α) (theta y)) =
      Function.uncurry F ∘ (fun y : R3 => (rho y ^ α, theta y)) := rfl
  rw [hfun, fderiv_comp x hFd hG]
  rw [ContinuousLinearMap.comp_apply]
  have hGe : (fderiv ℝ (fun y : R3 => (rho y ^ α, theta y)) x) (eTheta x) = (0, 0) := by
    rw [DifferentiableAt.fderiv_prodMk hrho htheta, ContinuousLinearMap.prod_apply,
      fderiv_Rpow_eTheta x hr α, fderiv_theta_eTheta x hr]
  rw [hGe]
  exact map_zero _

/-! ## The main theorem -/

theorem div_omegaS {p : ℝ} {g : ℝ → ℝ → ℝ} {x : Work.ConstructionInstance.R3}
    (hg : ContDiffAt ℝ 1 (Function.uncurry (Work.ConstructionInstance.profile p g))
      ((Work.Cyl.rho x) ^ p, Work.Cyl.theta x))
    (hr : 0 < Work.Cyl.radial x) :
    FiniteTimeSingularity.div (Work.ConstructionInstance.omegaS p g) x = 0 := by
  have hFd : DiffAt2 (profile p g) (rho x ^ p) (theta x) :=
    hg.differentiableAt (by norm_num)
  have hdiff : DifferentiableAt ℝ (fun y : R3 => profile p g (rho y ^ p) (theta y)) x :=
    differentiableAt_rhoPow_theta_comp (profile p g) p x hFd hr
  have hvdiff : DifferentiableAt ℝ eTheta x := differentiableAt_eTheta x hr
  have h1 : omegaS p g = (fun y : R3 => profile p g (rho y ^ p) (theta y)) • eTheta := by
    funext y
    show omegaS p g y = profile p g (rho y ^ p) (theta y) • eTheta y
    rw [omegaS_apply']
  rw [h1, div_smul_eq _ _ x hdiff hvdiff, div_eTheta x hr,
    fderiv_R_theta_eTheta (profile p g) p x hFd hr]
  ring

end Work.ConstructionInstance
