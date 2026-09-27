import Mathlib
import Submission.Work.Misiurewicz.exists_null_frontier_Vball_radius
import Submission.Work.EKLC6Core.frontier_Vball_null_of_continuousAt
import Submission.Work.EKLC6Core.exists_continuousAt_monotone_between

/-!
# A null-frontier radius in a prescribed interval `[a, b]`

`Work.EKLComp.Vball r z = V r • z` is the image of the "max-entry displacement" neighbourhood
`V r` of the identity of `SL₃(ℝ)` under the orbit map `u ↦ u • z` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`.
`Work.Misiurewicz.exists_null_frontier_Vball_radius` shows that, for every finite Borel measure
`ν` on `X₃`, every `z` and every `r₀ > 0`, some radius `r ∈ (0, r₀]` has `ν`-null frontier.

Here we record the quantitative refinement used by the cell-cover construction: the radius can be
chosen inside any *prescribed* interval `[a, b]` with `0 < a < b`.  Indeed the function
`t ↦ (ν (Vball t z)).toReal` is monotone, hence has only countably many points of discontinuity;
the complement of that countable set is dense, so it meets the open interval `(a, b)`.  Any such
continuity point `r > 0` has a `ν`-null frontier
(`Work.EKLC6Core.frontier_Vball_null_of_continuousAt`), which is the classical
"no jumps" argument: `closure (Vball r z) ⊆ Vball s z` for `s > r`, so for every `ε > 0`
right-continuity at `r` forces `ν (frontier (Vball r z)) = 0`.

This is the statement `Submission/Work/EKLC6Core/cell_cover_exists.lean` consumes.
-/

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open Work.EKLContract Work.EKLComp

noncomputable section

/-- For any finite measure `ν` on `X₃`, any `z : X₃` and any `0 < a < b` there is a radius
`r ∈ [a, b]` whose ball `Vball r z` has `ν`-null frontier. -/
theorem exists_null_frontier_Vball_radius_between (ν : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure ν] (z : Work.EKLContract.X3) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ r : ℝ, a ≤ r ∧ r ≤ b ∧ ν (frontier (Work.EKLComp.Vball r z)) = 0 := by
  obtain ⟨r, hra, hrb, hcont⟩ :=
    exists_continuousAt_monotone_between
      (f := fun t : ℝ => (ν (Work.EKLComp.Vball t z)).toReal)
      (fun s t hst =>
        ENNReal.toReal_mono (measure_ne_top ν _)
          (measure_mono (Work.Misiurewicz.Vball_mono z hst))) hab
  exact ⟨r, hra, hrb, frontier_Vball_null_of_continuousAt ν z (lt_of_lt_of_le ha hra) hcont⟩

end

end Work.EKLC6Core
