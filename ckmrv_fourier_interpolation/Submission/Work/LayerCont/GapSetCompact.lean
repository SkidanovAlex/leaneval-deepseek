/-
# The compact set on which the two-variable kernel bound is taken

`Work.LayerCont.gapSet K T A = (K ×ˢ Icc 1 T) ∩ {p | A ≤ |p.2 - p.1.im|}` is the region of the
gap-closer `Work.LayerCont.GapBoundKaxis`: the points `(τ,t)` with `τ ∈ K`, `1 ≤ t ≤ T` and the
guard `A ≤ |t - τ.im|` which keeps the contour point off the moving pole.

It is named (rather than written inline) because the compound term
`(K ×ˢ Icc 1 T) ∩ {p | A ≤ |p.2 - p.1.im|}` is heavily unfolded at every unification site that
mentions it, which is what made the first draft of the gap-closer exceed its elaboration budget.
-/
import Mathlib

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

/-- The region `K × [1,T]` cut by the guard `A ≤ |t - τ.im|`. -/
def gapSet (K : Set UpperHalfPlane) (T A : ℝ) : Set (UpperHalfPlane × ℝ) :=
  (K ×ˢ Set.Icc (1 : ℝ) T) ∩ {p : UpperHalfPlane × ℝ | A ≤ |p.2 - p.1.im|}

/-- **`gapSet` is compact** for compact `K`.  Intersection of the compact `K × [1,T]` with the
closed set `{p | A ≤ |p.2 - p.1.im|}` (`isClosed_le` against the continuous map
`p ↦ |p.2 - p.1.im|`). -/
theorem isCompact_gapSet {K : Set UpperHalfPlane} (hK : IsCompact K) (T A : ℝ) :
    IsCompact (gapSet K T A) := by
  have hcont : Continuous (fun p : UpperHalfPlane × ℝ => |p.2 - p.1.im|) := by fun_prop
  exact (hK.prod isCompact_Icc).inter_right (isClosed_le continuous_const hcont)

end Work.LayerCont
