import Mathlib
import Submission.Work.Whitney.PathTools.room_at_arc_subset

namespace Work.Whitney.PathTools

open Set Metric Topology Filter

/-- **Local room at a point of a compact arc-like set.**  If `h '' K` is the image of a compact
`K ⊆ ℝ` (with `h` continuous and injective on `K`), `n ≥ 3`, `y ∈ h '' K` and `N` is a
neighbourhood of `y`, then there is an open `O` with `y ∈ O`, `O ⊆ N`, `(O \ h '' K).Nonempty`
and `IsPreconnected (O \ h '' K)`.

This is exactly `Work.Whitney.PathTools.exists_local_room`, established together with the
"room at a point of a one-dimensional compact set" theorem `room_at_arc_subset` (slicing the
curve in a direction whose every slice is totally disconnected, and using the removal theorems
for compact totally disconnected sets in dimensions `≥ 2`). -/
theorem local_room_compact_arc_like {n : ℕ} (hn : 3 ≤ n) {K : Set ℝ} (hK : IsCompact K)
    {h : ℝ → EuclideanSpace ℝ (Fin n)} (hh : ContinuousOn h K) (hinj : Set.InjOn h K)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ h '' K) {N : Set (EuclideanSpace ℝ (Fin n))}
    (hN : N ∈ 𝓝 y) :
    ∃ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O ∧ y ∈ O ∧ O ⊆ N ∧
      (O \ h '' K).Nonempty ∧ IsPreconnected (O \ h '' K) :=
  exists_local_room hn hK hh hinj hy hN

end Work.Whitney.PathTools
