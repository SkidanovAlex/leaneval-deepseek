import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.Cyl.fderiv_angularVec_apply
import Submission.Work.Cyl.fderiv_radial_apply
import Submission.Work.Cyl.norm_angularVec
import Submission.Work.Cyl.inner_angularVec
import Submission.Work.Cyl.abs_inner_angularVec_le
import Submission.Work.CoreResiduals.VorticityEquation.fderiv_eTheta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses

/-!
# The derivative bound for the angular frame vector `e_θ`

`e_θ = (1/r) • angularVec` with `r = radial x = √(x₀² + x₁²)` and `angularVec x = (-x₁, x₀, 0)`.
Off the axis (`0 < radial x`) the product rule gives the Fréchet derivative
(`Work.CoreResiduals.VorticityEquation.fderiv_eTheta`)

`fderiv ℝ e_θ x v = (-(x₀v₀ + x₁v₁)/r³) • angularVec x + (1/r) • angularVec v`,

so, since `‖angularVec y‖ = radial y ≤ ‖y‖` (`Work.Cyl.norm_angularVec`,
`Work.Cyl.radial_le_rho` + `Work.Cyl.rho_eq_norm`) and
`|x₀v₀ + x₁v₁| = |⟪angularVec x, angularVec v⟫| ≤ r · radial v`
(`Work.Cyl.inner_angularVec`, `Work.Cyl.abs_inner_angularVec_le`),

`‖fderiv ℝ e_θ x v‖ ≤ (radial v / r) + (radial v / r) ≤ 2‖v‖/r`.

The constant `2` is the one the paper's weighted Lipschitz bound
(`Work.Cyl.eTheta_sub_norm_mul_le`) uses; it is sharp in the sense that the two summands each
contribute `‖v‖/r` with the same weight.

The statement (and its name) is unchanged from the request.
-/

theorem eTheta_deriv_bound (x : EuclideanSpace ℝ (Fin 3)) (hr : 0 < Work.Cyl.radial x) :
    DifferentiableAt ℝ Work.Cyl.eTheta x ∧
      ‖fderiv ℝ Work.Cyl.eTheta x‖ ≤ 2 / Work.Cyl.radial x := by
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  -- `radial v ≤ ‖v‖`, so the `angularVec`-factor is dominated by the norm
  have hrv_le : ∀ v : Work.Cyl.R3, Work.Cyl.radial v ≤ ‖v‖ := fun v => by
    rw [← Work.Cyl.rho_eq_norm]
    exact Work.Cyl.radial_le_rho v
  -- `angularVec` is differentiable: it is the linear map `y ↦ (-y₁) • e₀ + y₀ • e₁`
  have hAng : DifferentiableAt ℝ (fun y : Work.Cyl.R3 => Work.Cyl.angularVec y) x := by
    have h : (fun y : Work.Cyl.R3 => Work.Cyl.angularVec y) =
        fun y : Work.Cyl.R3 => (-y 1) • Work.Cyl.e0 + (y 0) • Work.Cyl.e1 := by
      funext y
      apply Work.Cyl.ext_coord <;>
        simp [Work.Cyl.angularVec, Work.Cyl.e0, Work.Cyl.e1, FiniteTimeSingularity.e]
    rw [h]; fun_prop
  -- `e_θ = r⁻¹ • angularVec`
  have hE : Work.Cyl.eTheta =
      (fun y : Work.Cyl.R3 => (Work.Cyl.radial y)⁻¹) • Work.Cyl.angularVec := by
    funext y
    show (1 / Work.Cyl.radial y) • Work.Cyl.angularVec y
      = (Work.Cyl.radial y)⁻¹ • Work.Cyl.angularVec y
    rw [one_div]
  refine ⟨?_, ?_⟩
  · rw [hE]
    exact ((Work.Cyl.differentiableAt_radial x hrne).inv hrne).smul hAng
  · rw [ContinuousLinearMap.opNorm_le_iff (by positivity : (0 : ℝ) ≤ 2 / Work.Cyl.radial x)]
    intro v
    rw [Work.CoreResiduals.VorticityEquation.fderiv_eTheta x v hr]
    -- `|x₀v₀ + x₁v₁| ≤ r · radial v`
    have hb : |x 0 * v 0 + x 1 * v 1| ≤ Work.Cyl.radial x * Work.Cyl.radial v := by
      rw [← Work.Cyl.inner_angularVec x v]
      exact Work.Cyl.abs_inner_angularVec_le x v
    -- the derivative of the radial weight: `≤ radial v / r`
    have hφ1 : ‖(-(x 0 * v 0 + x 1 * v 1) / (Work.Cyl.radial x) ^ 3) • Work.Cyl.angularVec x‖
        ≤ Work.Cyl.radial v / Work.Cyl.radial x := by
      rw [norm_smul, Real.norm_eq_abs, Work.Cyl.norm_angularVec, abs_div, abs_neg,
        abs_of_pos (by positivity : (0 : ℝ) < Work.Cyl.radial x ^ 3)]
      have key : |x 0 * v 0 + x 1 * v 1| / Work.Cyl.radial x ^ 3 * Work.Cyl.radial x
          = |x 0 * v 0 + x 1 * v 1| / Work.Cyl.radial x ^ 2 := by
        field_simp
      rw [key]
      have h := div_le_div_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ (Work.Cyl.radial x) ^ 2)
      have h2 : (Work.Cyl.radial x * Work.Cyl.radial v) / Work.Cyl.radial x ^ 2
          = Work.Cyl.radial v / Work.Cyl.radial x := by
        field_simp
      rwa [h2] at h
    -- the derivative of the linear factor: `≤ ‖v‖ / r`
    have hφ2 : ‖(Work.Cyl.radial x)⁻¹ • Work.Cyl.angularVec v‖ ≤ ‖v‖ / Work.Cyl.radial x := by
      rw [norm_smul, Real.norm_eq_abs, Work.Cyl.norm_angularVec,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Work.Cyl.radial x)⁻¹)]
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (hrv_le v)
        (by positivity : (0 : ℝ) ≤ (Work.Cyl.radial x)⁻¹)
    calc ‖(-(x 0 * v 0 + x 1 * v 1) / (Work.Cyl.radial x) ^ 3) • Work.Cyl.angularVec x
            + (Work.Cyl.radial x)⁻¹ • Work.Cyl.angularVec v‖
        ≤ ‖(-(x 0 * v 0 + x 1 * v 1) / (Work.Cyl.radial x) ^ 3) • Work.Cyl.angularVec x‖
            + ‖(Work.Cyl.radial x)⁻¹ • Work.Cyl.angularVec v‖ := norm_add_le _ _
      _ ≤ Work.Cyl.radial v / Work.Cyl.radial x + ‖v‖ / Work.Cyl.radial x := add_le_add hφ1 hφ2
      _ ≤ ‖v‖ / Work.Cyl.radial x + ‖v‖ / Work.Cyl.radial x :=
          add_le_add (div_le_div_of_nonneg_right (hrv_le v) (le_of_lt hr)) le_rfl
      _ = 2 / Work.Cyl.radial x * ‖v‖ := by ring

end Work.FTS.FireFix.Clauses
