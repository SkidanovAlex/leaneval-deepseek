import Mathlib
import Submission.Work.LinnikAreas.RepelDefs

/-!
# Basic properties of the triangular kernel `repelPsi`

`repelPsi u = ∫₀¹ e^{ut} (1 - t) dt` (see `RepelDefs`).  Here we record the two endpoint
values and monotonicity, which are the elementary inputs to the Deuring--Heilbronn engine:

* `repelPsi 0 = 1/2`,
* `repelPsi 1 = e - 2`,
* `u ↦ repelPsi u` is monotone (the integrand is increasing in `u` on `[0,1]` and `1 - t ≥ 0`).
-/

namespace Work.LinnikAreas

open MeasureTheory intervalIntegral

/-- The value at `0`: `∫₀¹ (1 - t) dt = 1/2`. -/
theorem repelPsi_zero : repelPsi 0 = 1 / 2 := by
  rw [repelPsi]
  simp only [zero_mul, Real.exp_zero, one_mul]
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_id]
  rw [intervalIntegral.integral_const, integral_id]
  norm_num

/-- The value at `1`: `∫₀¹ e^t (1 - t) dt = e - 2`, via the antiderivative `(2 - t) e^t`. -/
theorem repelPsi_one : repelPsi 1 = Real.exp 1 - 2 := by
  rw [repelPsi]
  simp only [one_mul]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => (2 - t) * Real.exp t)
    (f' := fun x : ℝ => Real.exp x * (1 - x)) ?_ ?_]
  · norm_num [Real.exp_zero]
  · intro x _
    have h1 : HasDerivAt (fun t : ℝ => 2 - t) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (c := (2 : ℝ))
    have h2 : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x
    have h3 := h1.mul h2
    refine h3.congr_deriv ?_
    ring
  · exact (by fun_prop :
      Continuous (fun x : ℝ => Real.exp x * (1 - x))).intervalIntegrable 0 1

/-- Monotonicity: for `u ≤ v` and `t ∈ [0,1]` we have `e^{ut} ≤ e^{vt}` and `1 - t ≥ 0`,
so the integrands are pointwise ordered. -/
theorem repelPsi_mono : Monotone repelPsi := by
  intro u v huv
  rw [repelPsi, repelPsi]
  refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
  · exact (by fun_prop :
      Continuous (fun t : ℝ => Real.exp (u * t) * (1 - t))).intervalIntegrable 0 1
  · exact (by fun_prop :
      Continuous (fun t : ℝ => Real.exp (v * t) * (1 - t))).intervalIntegrable 0 1
  · intro t ht
    rw [Set.mem_Icc] at ht
    obtain ⟨ht0, ht1⟩ := ht
    have hexp : Real.exp (u * t) ≤ Real.exp (v * t) := Real.exp_le_exp.mpr (by nlinarith)
    have h1t : (0 : ℝ) ≤ 1 - t := by linarith
    have hexp0 : (0 : ℝ) ≤ Real.exp (v * t) := (Real.exp_pos _).le
    exact mul_le_mul hexp le_rfl h1t hexp0

theorem repelPsiBasic : repelPsi 0 = 1 / 2 ∧ repelPsi 1 = Real.exp 1 - 2 ∧ Monotone repelPsi :=
  ⟨repelPsi_zero, repelPsi_one, repelPsi_mono⟩

end Work.LinnikAreas
