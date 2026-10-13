import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.StabilityFar.Basic
import Submission.Work.StabilityFar.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

/-- **`St4(b)` on the two-sided window `[-1, T+1]`, for any `T > -2`.**

If every time slice of `ω` in the window `window T = [-1, T+1]` is supported in the closed ball
of radius `R`, then so is every slice of `∂ₜω`.  The point is local in the time variable: for a
point `y` outside the ball, the function `s ↦ ω(y,s)` vanishes on *all* of `window T`, hence in
particular on a one-sided neighbourhood of any `t ∈ window T` (to the right when `t < T+1`, to
the left when `t = T+1`), and `timeDeriv_eq_zero_of_eq_zero_on_Ico` /
`timeDeriv_eq_zero_of_eq_zero_on_Ioc` then give `∂ₜω(y,t) = 0`.

Nothing about the sign of `T` is needed beyond the non-degeneracy of the window, whence the
hypothesis is only `-2 < T` (i.e. `-1 < T + 1`): the version `slicesSupported_timeDeriv` in
`Basic.lean` covers the case `0 ≤ T`. -/
theorem slicesSupported_timeDeriv_window {ω : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3}
    {R T : ℝ} (hT : -2 < T) (h : Work.StabilityFar.SlicesSupported ω R T) :
    Work.StabilityFar.SlicesSupported (FiniteTimeSingularity.timeDeriv ω) R T := by
  intro t ht y hy
  by_contra hmem
  -- `y` lies outside the ball of radius `R`, so every slice of `ω` at `y` vanishes on the window
  have hvan : ∀ s ∈ Work.StabilityFar.window T, ω y s = 0 := by
    intro s hs
    by_contra hne
    have hs' := h s hs y hne
    rw [Metric.mem_closedBall, dist_zero_right] at hs'
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    linarith
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · -- `t < T + 1`: `ω` vanishes on `[t, T+1)`, a right-neighbourhood of `t`
    refine hy (Work.StabilityFar.timeDeriv_eq_zero_of_eq_zero_on_Ico (ω := ω) (x := y) (t := t)
      (ε := T + 1 - t) (by linarith) ?_)
    intro s hs
    exact hvan s ⟨by linarith [hs.1, ht.1], by linarith [hs.2]⟩
  · -- `t = T + 1`: `ω` vanishes on `(-1, t]`, a left-neighbourhood of `t`
    refine hy (Work.StabilityFar.timeDeriv_eq_zero_of_eq_zero_on_Ioc (ω := ω) (x := y) (t := t)
      (ε := T + 2) (by linarith) ?_)
    intro s hs
    exact hvan s ⟨by linarith [hs.1], by linarith [heq, hs.2]⟩

end Work.StabilityFar.Decay
