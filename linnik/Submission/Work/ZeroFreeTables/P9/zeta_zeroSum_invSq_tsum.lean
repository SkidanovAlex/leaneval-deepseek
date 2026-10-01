import Mathlib
import Submission.Work.LinnikAreas.xiCZeroInvSqTailBound
import Submission.Work.LinnikAreas.PrincipalZeroCount
import Submission.Work.LinnikAreas.FarRepel.zeroSumInvSqBound

namespace Work.ZeroFreeTables.P9

/-- On the fixed compact set `‖s‖ ≤ 11` the multiplicity-weighted inverse-square kernel sum
over the zeros of the completed Riemann zeta function is bounded.

This is the compact-set specialization of the (uniform in `w`) kernel bound
`Work.LinnikAreas.FarRepel.zetaHalfKernelBound`
`∑' u, ord_u(Λ) · (1/(1+‖w-u‖²)) ≤ C · (log (2 + ‖w‖) + 2)`:
for `‖s‖ ≤ 11` the factor `log (2 + ‖s‖) + 2` is at most `log 13 + 2`. -/
theorem zeta_zeroSum_invSq_tsum :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ‖s‖ ≤ 11 →
      (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))
        ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := Work.LinnikAreas.FarRepel.zetaHalfKernelBound
  have hlog13 : (0 : ℝ) < Real.log 13 + 2 := by
    have h : (0 : ℝ) < Real.log 13 := Real.log_pos (by norm_num)
    linarith
  refine ⟨C * (Real.log 13 + 2) + 1, by positivity, fun s hs => ?_⟩
  have hsum := (hC s).2
  have hlog : Real.log (2 + ‖s‖) ≤ Real.log 13 := by
    apply Real.log_le_log (by positivity)
    linarith [norm_nonneg s]
  calc (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))
      ≤ C * (Real.log (2 + ‖s‖) + 2) := hsum
    _ ≤ C * (Real.log 13 + 2) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hCpos)
        linarith
    _ ≤ C * (Real.log 13 + 2) + 1 := by linarith

end Work.ZeroFreeTables.P9
