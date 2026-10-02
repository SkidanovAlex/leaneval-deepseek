import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_XiStrip
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_WindowZeroCountOfUnit

namespace Work.LinnikAreas.DhExplicit

/-!
# Zero count of `Ξ` in a window of height `h`

`Work.LinnikAreas.DhK.Xi` is the entire completion of the Riemann zeta function.  The hypothesis
`hunit` is the unit-window count for `Ξ` (sibling module
`Submission.Work.LinnikAreas.DhExplicit.XiUnitWindowCount`), i.e. the statement that for every `t`
and every finite `S` with `|u.im - t| ≤ 1` one has
`∑_{u∈S} ord_u(Ξ) ≤ C (log (2 + |t|) + 2)`.

The conclusion covers a window of *arbitrary* height `h ≥ 1`: for every finite `S` with
`|u.im - t| ≤ h`, `∑_{u∈S} ord_u(Ξ) ≤ C (h+1) (log (2 + |t| + h) + 2)`.

Proof: this is exactly `Work.LinnikAreas.FarRepel.lamWindowZeroCount`
(module `Submission.Work.LinnikAreas.FarRepel.zeroSumInvSqBound`, not importable here — read and
copy; it pulls in `completedL_pf_identity_rect`, whose `pfP` clashes with
`logDeriv_pf_identity`).  Cover `[-h,h]` about `t` by the windows `[t ± 2j - 1, t ± 2j + 1]`,
`j ≤ ⌊h/2 + 1⌋`, via `window_cover_index` in that same file, apply `hunit` to each unit window
and sum: the `⌊h/2+1⌋+1 ≤ h+2` windows cost `≤ (h+2)·C·(log (2 + |t| + h + 2) + 2)`, and
`log (2 + |t| + h + 2) ≤ log (2 + |t| + h) + 2`, `h + 2 ≤ 2(h+1)` absorb into the stated shape.
-/
theorem XiWindowCount
    (hunit : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ∀ S : Finset ℂ, (∀ u ∈ S, |u.im - t| ≤ 1) →
      ∑ u ∈ S, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ)
        ≤ C * (Real.log (2 + |t|) + 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t h : ℝ), 1 ≤ h → ∀ S : Finset ℂ, (∀ u ∈ S, |u.im - t| ≤ h) →
      ∑ u ∈ S, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ)
        ≤ C * (h + 1) * (Real.log (2 + |t| + h) + 2) := by
  obtain ⟨C, hC, h⟩ := hunit
  exact WindowZeroCountOfUnit Work.LinnikAreas.DhK.Xi C hC h

end Work.LinnikAreas.DhExplicit
