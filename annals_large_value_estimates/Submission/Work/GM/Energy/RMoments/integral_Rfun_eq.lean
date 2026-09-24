import Mathlib
import Submission.Work.GM.Energy.RMoments.FejerDefs

namespace Work.GM.Energy.RMoments

open Complex Finset
open scoped BigOperators

set_option autoImplicit false

/-- For a positive real base `x` and a real exponent `t`, the complex power `x^{it}` is the
exponential `e^{i t log x}`. -/
lemma ofReal_cpow_I_mul (x : ℝ) (hx : 0 < x) (t : ℝ) :
    (((x : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)))
      = Complex.exp (Complex.I * ((t * Real.log x : ℝ) : ℂ)) := by
  have hx0 : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le]
  congr 1
  push_cast
  ring

/-- `Rfun W (e^u) = expSum W u`, i.e. `R` evaluated at `v = e^u` is the exponential sum
`Σ_{t ∈ W} e^{i t u}`. -/
lemma Rfun_exp_eq_expSum (W : Finset ℝ) (u : ℝ) :
    Submission.GM.Rfun W (Real.exp u) = expSum W u := by
  simp only [Submission.GM.Rfun, expSum, Real.abs_exp]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [ofReal_cpow_I_mul (Real.exp u) (Real.exp_pos u) t, Real.log_exp]

/-- Substitution `v = e^u`: the integral of `‖Rfun W v‖⁴` over `v ∈ [1,2]` equals the integral of
`‖expSum W u‖⁴ e^u` over `u ∈ [0, log 2]`. -/
theorem integral_Rfun_eq (W : Finset ℝ) :
    (∫ v in (1:ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 4)
      = ∫ u in (0:ℝ)..Real.log 2, ‖expSum W u‖ ^ 4 * Real.exp u := by
  have hsub : (∫ u in (0:ℝ)..Real.log 2,
        ‖Submission.GM.Rfun W (Real.exp u)‖ ^ 4 * Real.exp u)
      = ∫ v in (1:ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 4 := by
    have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0:ℝ)) (b := Real.log 2) (f := Real.exp) (f' := Real.exp)
      (g := fun v : ℝ => ‖Submission.GM.Rfun W v‖ ^ 4)
      Real.continuous_exp.continuousOn
      (fun x _ => Real.hasDerivAt_exp x)
      (fun x _ => (Real.exp_pos x).le)
    rw [Real.exp_zero, Real.exp_log (by norm_num : (0:ℝ) < 2)] at h
    simpa only [Function.comp_apply] using h
  rw [← hsub]
  simp only [Rfun_exp_eq_expSum]

end Work.GM.Energy.RMoments
