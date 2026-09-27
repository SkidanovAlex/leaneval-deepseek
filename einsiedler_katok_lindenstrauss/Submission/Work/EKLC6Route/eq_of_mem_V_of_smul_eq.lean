import Mathlib
import Submission.Work.EKLC6Route.Defs

namespace Work.EKLC6Route

/-- Two elements of `V w.δ` that agree on a point `z` of the window `W` are equal.

Indeed `z ∈ W = chartSet t w.z0 w.uc w.θ w.r w.ρ` means `z = (u * k) • w.z0` with
`u = w.uc z ∈ Uball (Uminus t) w.r` and `k = w.θ z ∈ VtSet t ∩ V w.ρ`; since `w.r, w.ρ > 0`
these are also in `Uball (Uminus t) (2 * w.r)` and `VtSet t ∩ V (2 * w.ρ)`, so the chart's
injectivity clause `Chart.inj` applies verbatim. -/
theorem eq_of_mem_V_of_smul_eq {μ : MeasureTheory.Measure Work.EKLContract.X3} {t : Fin 3 → ℝ}
    (w : Work.EKLC6Route.Window μ t) {z : Work.EKLContract.X3} (hz : z ∈ w.W)
    {g h : Work.EKLContract.SL3} (hg : g ∈ Work.EKLContract.V w.δ)
    (hh : h ∈ Work.EKLContract.V w.δ) (heq : g • z = h • z) : g = h := by
  -- Unfold the membership `z ∈ W = chartSet t w.z0 w.uc w.θ w.r w.ρ`.
  obtain ⟨hzu, hzk, hzmk⟩ := hz
  -- Apply the injectivity clause of the chart, enlarging `w.r`, `w.ρ` to `2 * w.r`, `2 * w.ρ`.
  refine w.inj (w.uc z) ?_ (w.θ z) ?_ g h hg hh ?_
  · obtain ⟨hmem, hdev⟩ := hzu
    exact ⟨hmem, fun i j => lt_of_lt_of_le (hdev i j) (by linarith [w.hr])⟩
  · refine ⟨hzk.1, fun i j => lt_of_lt_of_le (hzk.2 i j) (by linarith [w.hρ])⟩
  · rw [hzmk]; exact heq

end Work.EKLC6Route
