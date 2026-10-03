import Mathlib

namespace Work.FIArea6Hecke.R

/-- If `Λ` is analytic on the closed ball of radius `T` around `0` and the divisor of `Λ` on
that ball is nonzero at `u`, then `u` lies in the ball (`‖u‖ ≤ T`), `Λ u = 0`, and the divisor
is nonnegative at `u`.

Indeed, a nonzero divisor forces `u` into the ball (outside of it the divisor vanishes by
definition); there `Λ` is meromorphic, hence the divisor is `(meromorphicOrderAt Λ u).untop₀`,
which is nonzero. Since `Λ` is analytic at `u`, its meromorphic order is nonnegative, so it is
in fact strictly positive; equivalently the analytic order is nonzero, which forces `Λ u = 0`.
Nonnegativity of the divisor follows from nonnegativity of the meromorphic order together with
`WithTop.untop₀_nonneg`. -/
theorem divisorSupportFacts {Λ : ℂ → ℂ} {T : ℝ}
    (hAn : AnalyticOnNhd ℂ Λ (Metric.closedBall 0 T)) {u : ℂ}
    (hu : (MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u ≠ 0) :
    Λ u = 0 ∧ ‖u‖ ≤ T ∧ 0 ≤ (MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u := by
  have hmem : u ∈ Metric.closedBall 0 T := by
    by_contra h
    exact hu (by rw [MeromorphicOn.divisor_def]; simp [h])
  have hmer : MeromorphicOn Λ (Metric.closedBall 0 T) := hAn.meromorphicOn
  have hval : (MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u =
      (meromorphicOrderAt Λ u).untop₀ := MeromorphicOn.divisor_apply hmer hmem
  have h1 : (meromorphicOrderAt Λ u).untop₀ ≠ 0 := by rw [hval] at hu; exact hu
  have han : AnalyticAt ℂ Λ u := hAn u hmem
  have hnonneg : 0 ≤ meromorphicOrderAt Λ u := han.meromorphicOrderAt_nonneg
  refine ⟨?_, ?_, ?_⟩
  · rw [han.meromorphicOrderAt_eq] at h1
    refine apply_eq_zero_of_analyticOrderAt_ne_zero ?_
    intro hz
    rw [hz] at h1
    simp at h1
  · rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact hmem
  · rw [hval]
    exact (WithTop.untop₀_nonneg).2 hnonneg

end Work.FIArea6Hecke.R
