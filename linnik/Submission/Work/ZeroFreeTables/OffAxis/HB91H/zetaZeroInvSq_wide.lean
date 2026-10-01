import Mathlib
import Submission.Work.LinnikAreas.FarRepel.zeroSumInvSqBound

/-!
# `Work.ZeroFreeTables.OffAxis.HB91H.zetaZeroInvSq_wide`

The Poisson-kernel (inverse-square) zero sum of the completed Riemann zeta function,
`∑' u, ord_u(Λ) · 1/(1 + ‖s - u‖²)`, is bounded uniformly for `‖s‖ ≤ T`, for every `T > 0`.

This is a direct consequence of the uniform-in-`w` kernel bound
`Work.LinnikAreas.FarRepel.zetaHalfKernelBound`,

  `∑' u, ord_u(Λ) · 1/(1 + ‖w - u‖²) ≤ C · (log (2 + ‖w‖) + 2)`   for all `w : ℂ`,

by bounding the right-hand side on the closed disk `‖s‖ ≤ T`: the factor `log (2 + ‖s‖) + 2` is
at most `log (2 + T) + 2`, which is a positive constant.
-/

open Complex

namespace Work.ZeroFreeTables.OffAxis.HB91H

noncomputable section

theorem zetaZeroInvSq_wide (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ‖s‖ ≤ T →
      (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))
        ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := Work.LinnikAreas.FarRepel.zetaHalfKernelBound
  have hlogpos : 0 < Real.log (2 + T) + 2 := by
    have h2T : (0 : ℝ) < 2 + T := by linarith
    have : 0 < Real.log (2 + T) := Real.log_pos (by linarith)
    linarith
  refine ⟨C * (Real.log (2 + T) + 2), by positivity, fun s hs => ?_⟩
  have hb := (hC s).2
  have hmono : Real.log (2 + ‖s‖) ≤ Real.log (2 + T) := by
    apply Real.log_le_log
    · positivity
    · linarith [norm_nonneg s]
  calc (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))
      ≤ C * (Real.log (2 + ‖s‖) + 2) := hb
    _ ≤ C * (Real.log (2 + T) + 2) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hCpos)
        linarith


end

end Work.ZeroFreeTables.OffAxis.HB91H
