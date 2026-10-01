import Mathlib

namespace Work.LinnikAreas.Zeta1Aux

/-- If an entire function `f` has a nonzero divisor at a point `u` (measured on the closed ball
`closedBall c r`), then `f` vanishes at `u` and `u` lies in that closed ball. -/
lemma divisor_ne_zero_imp {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {r : ℝ} {u : ℂ}
    (h : MeromorphicOn.divisor f (Metric.closedBall c r) u ≠ 0) :
    f u = 0 ∧ u ∈ Metric.closedBall c r := by
  -- an entire function is meromorphic on every set
  have hmero : MeromorphicOn f (Metric.closedBall c r) := by
    intro z _
    exact (hf.differentiableOn.analyticAt Filter.univ_mem).meromorphicAt
  -- first, `u` must lie in the closed ball, else the divisor vanishes outside its domain
  have hu : u ∈ Metric.closedBall c r := by
    by_contra hu
    rw [MeromorphicOn.divisor_def] at h
    simp only [hmero, hu, true_and, if_false] at h
    exact h rfl
  refine ⟨?_, hu⟩
  -- on the ball the divisor is the order of vanishing, and a nonvanishing point has order `0`
  rw [MeromorphicOn.divisor_apply hmero hu] at h
  by_contra hfu
  have hord : meromorphicOrderAt f u = 0 :=
    ((hf.differentiableOn.analyticAt Filter.univ_mem).meromorphicNFAt).meromorphicOrderAt_eq_zero_iff.mpr
      hfu
  rw [hord, WithTop.untop₀_zero] at h
  exact h rfl

end Work.LinnikAreas.Zeta1Aux
