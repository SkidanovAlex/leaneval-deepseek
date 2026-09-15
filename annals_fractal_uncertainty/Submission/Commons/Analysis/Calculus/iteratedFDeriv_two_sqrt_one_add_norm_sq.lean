import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonneg_of_localMin

open scoped RealInnerProductSpace
open scoped Topology
open Filter

namespace Commons.Analysis.Calculus

/-- Along the line `t ↦ x + t • v`, the function `z ↦ 1 + ‖z‖ ^ 2` agrees with the quadratic
`1 + ‖x‖ ^ 2 + 2 * ⟪x, v⟫ * t + ‖v‖ ^ 2 * t ^ 2`. -/
theorem one_add_norm_add_smul_sq_eq {d : ℕ} (x v : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    1 + ‖x + t • v‖ ^ 2 = (1 + ‖x‖ ^ 2) + 2 * (inner ℝ x v) * t + ‖v‖ ^ 2 * t ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow]
  rw [Real.norm_eq_abs, sq_abs]
  ring

/-- Derivative of `t ↦ 1 + ‖x + t • v‖ ^ 2`. -/
theorem hasDerivAt_one_add_norm_add_smul_sq {d : ℕ} (x v : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => 1 + ‖x + t • v‖ ^ 2)
      (2 * (inner ℝ x v) + 2 * ‖v‖ ^ 2 * t) t := by
  have h1 : HasDerivAt (fun s : ℝ => 2 * (inner ℝ x v) * s) (2 * (inner ℝ x v)) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * (inner ℝ x v))
  have h2 : HasDerivAt (fun s : ℝ => ‖v‖ ^ 2 * s ^ 2) (‖v‖ ^ 2 * (2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_mul (‖v‖ ^ 2)
  have h3 := ((hasDerivAt_const (x := t) ((1 + ‖x‖ ^ 2))).add h1).add h2
  have hfun : ((fun _ : ℝ => 1 + ‖x‖ ^ 2) + fun s : ℝ => 2 * (inner ℝ x v) * s)
      + (fun s : ℝ => ‖v‖ ^ 2 * s ^ 2)
      = fun s : ℝ => (1 + ‖x‖ ^ 2) + 2 * (inner ℝ x v) * s + ‖v‖ ^ 2 * s ^ 2 := by
    funext s; simp only [Pi.add_apply]
  have hval : (0 + 2 * (inner ℝ x v) + ‖v‖ ^ 2 * (2 * t))
      = 2 * (inner ℝ x v) + 2 * ‖v‖ ^ 2 * t := by ring
  rw [hfun, hval] at h3
  rw [← funext (one_add_norm_add_smul_sq_eq x v)] at h3
  exact h3

/-- The second derivative at `0` of `t ↦ √(1 + ‖x + t • v‖ ^ 2)` (equivalently, the second
derivative of `z ↦ √(1 + ‖z‖ ^ 2)` at `x` in the direction `v`, twice). -/
theorem deriv_deriv_sqrt_one_add_norm_sq_line {d : ℕ} (x v : EuclideanSpace ℝ (Fin d)) :
    deriv (deriv (fun t : ℝ => Real.sqrt (1 + ‖x + t • v‖ ^ 2))) 0
      = ‖v‖ ^ 2 / Real.sqrt (1 + ‖x‖ ^ 2)
        - (inner ℝ x v) ^ 2 / (Real.sqrt (1 + ‖x‖ ^ 2)) ^ 3 := by
  have hqderiv := hasDerivAt_one_add_norm_add_smul_sq x v
  have hsq : ∀ t : ℝ, (1 : ℝ) + ‖x + t • v‖ ^ 2 ≠ 0 := by intro t; positivity
  have hsqderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.sqrt (1 + ‖x + t • v‖ ^ 2))
      ((2 * (inner ℝ x v) + 2 * ‖v‖ ^ 2 * t) / (2 * Real.sqrt (1 + ‖x + t • v‖ ^ 2))) t :=
    fun t => (hqderiv t).sqrt (hsq t)
  have hderiv_eq : deriv (fun t : ℝ => Real.sqrt (1 + ‖x + t • v‖ ^ 2)) =ᶠ[𝓝 (0:ℝ)]
      (fun t : ℝ => (inner ℝ x v + ‖v‖ ^ 2 * t) / Real.sqrt (1 + ‖x + t • v‖ ^ 2)) := by
    filter_upwards with t
    rw [(hsqderiv t).deriv]
    field_simp
  rw [hderiv_eq.deriv_eq]
  have hu : HasDerivAt (fun t : ℝ => inner ℝ x v + ‖v‖ ^ 2 * t) (‖v‖ ^ 2) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => ‖v‖ ^ 2 * t) (‖v‖ ^ 2) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_mul (‖v‖ ^ 2)
    simpa using h1.const_add (inner ℝ x v)
  have hw : HasDerivAt (fun t : ℝ => Real.sqrt (1 + ‖x + t • v‖ ^ 2))
      (inner ℝ x v / Real.sqrt (1 + ‖x‖ ^ 2)) 0 := by
    have h := (hqderiv 0).sqrt (hsq 0)
    rw [show (2 * (inner ℝ x v) + 2 * ‖v‖ ^ 2 * (0:ℝ))
          / (2 * Real.sqrt (1 + ‖x + (0:ℝ) • v‖ ^ 2))
        = inner ℝ x v / Real.sqrt (1 + ‖x‖ ^ 2) from by
      simp only [zero_smul, add_zero, mul_zero, add_zero]
      field_simp] at h
    exact h
  have hwne : Real.sqrt (1 + ‖x + (0:ℝ) • v‖ ^ 2) ≠ 0 := by positivity
  have hdiv := hu.div hw hwne
  rw [show (fun t : ℝ => (inner ℝ x v + ‖v‖ ^ 2 * t) / Real.sqrt (1 + ‖x + t • v‖ ^ 2))
      = ((fun t : ℝ => inner ℝ x v + ‖v‖ ^ 2 * t)
          / fun t : ℝ => Real.sqrt (1 + ‖x + t • v‖ ^ 2)) from rfl]
  rw [hdiv.deriv]
  simp only [zero_smul, add_zero, mul_zero]
  field_simp

theorem iteratedFDeriv_two_sqrt_one_add_norm_sq {d : ℕ} (x v : EuclideanSpace ℝ (Fin d)) :
    (iteratedFDeriv ℝ 2 (fun z : EuclideanSpace ℝ (Fin d) => Real.sqrt (1 + ‖z‖ ^ 2)) x) ![v, v]
      = ‖v‖ ^ 2 / Real.sqrt (1 + ‖x‖ ^ 2)
        - (inner ℝ x v) ^ 2 / (Real.sqrt (1 + ‖x‖ ^ 2)) ^ 3 := by
  have hcont : ContDiffAt ℝ 2 (fun z : EuclideanSpace ℝ (Fin d) => Real.sqrt (1 + ‖z‖ ^ 2)) x := by
    have h : ContDiff ℝ 2 (fun z : EuclideanSpace ℝ (Fin d) => Real.sqrt (1 + ‖z‖ ^ 2)) := by
      refine (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun z => ?_)
      positivity
    exact h.contDiffAt
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Commons.Analysis.Calculus.FDeriv.deriv_deriv_comp_line hcont v]
  exact deriv_deriv_sqrt_one_add_norm_sq_line x v

end Commons.Analysis.Calculus