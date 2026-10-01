import Mathlib
import Submission.Work.ZeroFreeTables.tf72Phi_defs
import Submission.Work.ZeroFreeTables.tf72Phi_neg_sum_integral

noncomputable section
open scoped Real
open MeasureTheory

namespace Work.ZeroFreeTables

/-- The polynomial body `(2-s)^3(4+6s+s^2)` of HB Lemma 7.2's test function is
non-negative on `[0,2]`. -/
lemma tf72Body_nonneg_of_mem (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 2) : 0 ≤ tf72Body s := by
  obtain ⟨hs0, hs2⟩ := hs
  rw [tf72Body]
  refine mul_nonneg ?_ ?_
  · have : 0 ≤ 2 - s := by linarith
    positivity
  · nlinarith [sq_nonneg (s + 3)]

/-- `tf72PhiLBneg x ≤ tf72Phi (-x)` for `0 ≤ x ≤ 2`: on `[0,2]` the exponential
`e^{xs}` dominates every partial sum of its Taylor series, and the polynomial
body is non-negative there, so integrating the degree-`8` partial sum and using
`∫₀² s^m (2-s)^3(4+6s+s²) ds = tf72M m` gives the lower bound. -/
theorem tf72Phi_neg_lower (x : ℝ) (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    tf72PhiLBneg x ≤ tf72Phi (-x) := by
  have hbody : ∀ s ∈ Set.Icc (0:ℝ) 2, 0 ≤ tf72Body s := tf72Body_nonneg_of_mem
  have hpt : ∀ s ∈ Set.Icc (0:ℝ) 2,
      (∑ m ∈ Finset.range 9, (x * s) ^ m / (m.factorial : ℝ)) * tf72Body s
        ≤ Real.exp (x * s) * tf72Body s := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    exact mul_le_mul_of_nonneg_right
      (Real.sum_le_exp_of_nonneg (mul_nonneg hx0 hs0) 9) (hbody s hs)
  have hint1 : IntervalIntegrable
      (fun s : ℝ => (∑ m ∈ Finset.range 9, (x * s) ^ m / (m.factorial : ℝ)) * tf72Body s)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    unfold tf72Body
    fun_prop
  have hint2 : IntervalIntegrable (fun s : ℝ => Real.exp (x * s) * tf72Body s)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous fun s : ℝ => Real.exp (x * s)) |>.mul
      (by unfold tf72Body; fun_prop)
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (a := (0:ℝ)) (b := 2)
    (by norm_num) hint1 hint2 hpt
  have hsum := tf72Phi_neg_sum_integral x
  have hfinal : (∑ m ∈ Finset.range 9, x ^ m * tf72M m / (m.factorial : ℝ))
      ≤ ∫ s in (0:ℝ)..2, Real.exp (x * s) * tf72Body s := by
    rw [← hsum]
    exact hmono
  rw [tf72PhiLBneg, tf72Phi]
  have hexp : (∫ s in (0:ℝ)..2, Real.exp (-((-x) * s)) * tf72Body s)
      = ∫ s in (0:ℝ)..2, Real.exp (x * s) * tf72Body s := by
    apply intervalIntegral.integral_congr
    intro s _
    show Real.exp (-((-x) * s)) * tf72Body s = Real.exp (x * s) * tf72Body s
    rw [show -((-x) * s) = x * s by ring]
  rw [hexp]
  exact mul_le_mul_of_nonneg_left hfinal (by norm_num)

end Work.ZeroFreeTables
