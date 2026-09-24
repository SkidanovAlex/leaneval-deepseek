/-
# `APSwitchUpper.oddSum_int_eq` — the integral of the first odd level on `[2,x]`

For `2 ≤ x ≤ 4` the first odd level `oddSum (n+1)` has the closed form
(`oddSum_formula`, i.e. the summed odd recursion with the even formula on `[1,3]`)

  `u · oddSum (n+1) u = (3 + Cv n)·log(3/(u−1)) − 4 + u + Tv (n+1)`,  `2 ≤ u ≤ 4`,

hence

  `oddSum (n+1) u = (3 + Cv n)·log(3/(u−1))/u + (Tv (n+1) − 4)/u + 1`.

Integrating over `[2,x]` and using `∫_2^x log(3/(u−1))/u = Aprime x`,
`∫_2^x u⁻¹ = log(x/2)`, `∫_2^x 1 = x − 2` gives the stated identity, which is the
generalization to a variable right endpoint of `integral_oddSum_Icc` (the case `x = 4`).
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiLevelCore
import Submission.Work.NumberTheory.Chen.APSwitchUpper.oddSum_formula
import Submission.Work.NumberTheory.Chen.APSwitchUpper.integral_oddSum_Icc

namespace Work.NumberTheory.Chen.APSwitchUpper

open MeasureTheory

theorem oddSum_int_eq (n : ℕ) {x : ℝ} (h2 : 2 ≤ x) (h4 : x ≤ 4) :
    (∫ u in (2 : ℝ)..x, oddSum (n + 1) u)
      = (3 + Cv n) * Aprime x + (Tv (n + 1) - 4) * Real.log (x / 2) + (x - 2) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hform : ∀ u ∈ Set.uIcc (2 : ℝ) x, oddSum (n + 1) u
      = (3 + Cv n) * (Real.log (3 / (u - 1)) / u) + (Tv (n + 1) - 4) * u⁻¹ + 1 := by
    intro u hu
    rw [Set.uIcc_of_le h2, Set.mem_Icc] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have hdiv : oddSum (n + 1) u
        = ((3 + Cv n) * Real.log (3 / (u - 1)) - 4 + u + Tv (n + 1)) / u := by
      rw [eq_div_iff hu0, mul_comm]
      exact oddSum_formula n hu.1 (le_trans hu.2 h4)
    rw [hdiv]; field_simp; ring
  rw [intervalIntegral.integral_congr hform]
  have hcont : ContinuousOn (fun u : ℝ => Real.log (3 / (u - 1)) / u) (Set.uIcc (2 : ℝ) x) := by
    refine ContinuousOn.div ?_ continuousOn_id (fun u hu => ?_)
    · refine ContinuousOn.log (ContinuousOn.div continuousOn_const
        (continuousOn_id.sub continuousOn_const) ?_) ?_
      · intro u hu; rw [Set.uIcc_of_le h2, Set.mem_Icc] at hu; linarith [hu.1]
      · intro u hu; rw [Set.uIcc_of_le h2, Set.mem_Icc] at hu
        have hx1 : 0 < u - 1 := by linarith [hu.1]
        exact ne_of_gt (by positivity)
    · rw [Set.uIcc_of_le h2, Set.mem_Icc] at hu; linarith [hu.1]
  have hI1 : IntervalIntegrable (fun u : ℝ => (3 + Cv n) * (Real.log (3 / (u - 1)) / u))
      volume (2 : ℝ) x := (hcont.const_mul (3 + Cv n)).intervalIntegrable
  have hI2 : IntervalIntegrable (fun u : ℝ => (Tv (n + 1) - 4) * u⁻¹) volume (2 : ℝ) x := by
    refine ((ContinuousOn.inv₀ (f := fun x : ℝ => x) continuousOn_id ?_).const_mul
      (Tv (n + 1) - 4)).intervalIntegrable
    intro u hu
    rw [Set.uIcc_of_le h2, Set.mem_Icc] at hu
    linarith [hu.1]
  have hI3 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (2 : ℝ) x := intervalIntegrable_const
  rw [intervalIntegral.integral_add (hI1.add hI2) hI3, intervalIntegral.integral_add hI1 hI2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_inv_of_pos (by norm_num : (0 : ℝ) < 2) hx0, integral_one]
  have hApr : (∫ u in (2 : ℝ)..x, Real.log (3 / (u - 1)) / u) = Aprime x := rfl
  simp only [hApr]

end Work.NumberTheory.Chen.APSwitchUpper
