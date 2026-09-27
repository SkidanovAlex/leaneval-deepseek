import Mathlib

/-!
# A compact set between a compact set and an open neighbourhood

`exists_isCompact_between`: for compact `K` inside an open `U` in a locally compact metric space there
is a compact `L` with `K ⊆ L ⊆ U` (a `cthickening` of `K`, chosen small enough to stay in `U`).

This is what lets the M1 assembly (`CutPush/NOTES_STATE_S59.md` §6.5) cut the chart-local families off
on a *compact* set inside the region where they are correct: the cut-off on the `E` side is built from
the *image* of that compact set, which is compact and lies in the chart's target.
-/

namespace Work.Whitney.CutPush

open Topology Metric

/-- **A compact set between a compact set and an open neighbourhood.** -/
theorem exists_isCompact_between {E : Type*} [PseudoMetricSpace E] [LocallyCompactSpace E]
    {U : Set E} (hU : IsOpen U) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : Set E, IsCompact L ∧ K ⊆ L ∧ L ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨δ', hδ', hδ'cpt⟩ := hK.exists_isCompact_cthickening
  refine ⟨cthickening (min δ δ') K, ?_, ?_, ?_⟩
  · exact IsCompact.of_isClosed_subset hδ'cpt isClosed_cthickening
      (cthickening_mono (min_le_right _ _) K)
  · exact subset_closure.trans (Metric.closure_subset_cthickening (min δ δ') K)
  · exact (cthickening_mono (min_le_left _ _) K).trans hδU

end Work.Whitney.CutPush
