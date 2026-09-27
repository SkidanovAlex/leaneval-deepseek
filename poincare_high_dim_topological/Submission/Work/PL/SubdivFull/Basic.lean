import Submission.Work.PL.SubdivFull.Defs
import Submission.Work.PL.Subdiv.Util.union_of_faces_sdIter

/-!
# Basic API of unions of closed faces

* `IsFaceUnion.sdIter` : a union of closed faces of `K` is a union of closed faces of `sdIter r K`
  (the `SubdivTools.subsp` field, for the concrete barycentric subdivision).
* `IsFaceUnion.sd` : the one-step case.
* `isFaceUnion_finset` / `isFaceUnion_iff` : presentations of a face union, by a finite or
  arbitrary family of faces.
* `fullOn_iff_filter` : the "filtered vertices" form of fullness.
-/

open Set Metric
open PL

namespace Work.PL.SubdivFull

noncomputable section

variable {N : ℕ}

/-- **A union of closed faces of `K` is a union of closed faces of any subdivision of `K`.** -/
theorem IsFaceUnion.sdIter {K : PL.Cx N} {L : Set (PL.E N)} (h : IsFaceUnion K L)
    (hK : K.faces.Finite) (r : ℕ) : IsFaceUnion (Work.PL.Subdiv.sdIter r K hK) L := by
  obtain ⟨T', hT'faces, hT'union⟩ :=
    Work.PL.Subdiv.Util.union_of_faces_sdIter h.1 h.2 r hK
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [show (Work.PL.Subdiv.sdIter r K hK).space = K.space from
      (Work.PL.Subdiv.sdIter_subdivides r K hK).1]
    exact h.1 hx
  · rw [hT'union] at hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    refine ⟨t, hT'faces t ht, hxt, fun y hy => ?_⟩
    rw [hT'union]
    exact mem_iUnion₂.mpr ⟨t, ht, hy⟩

/-- The one-step case of `IsFaceUnion.sdIter`. -/
theorem IsFaceUnion.sd {K : PL.Cx N} {L : Set (PL.E N)} (h : IsFaceUnion K L)
    (hK : K.faces.Finite) : IsFaceUnion (Work.PL.Subdiv.sd K) L := h.sdIter hK 1

/-- **Fullness in the "filtered vertices" form**: it suffices to test, on every face `s`, the set
`vertsIn s L` of vertices of `s` lying in `L`. -/
theorem fullOn_iff_filter (K' : PL.Cx N) (L : Set (PL.E N)) :
    FullOn K' L ↔ ∀ s ∈ K'.faces, PL.simp (vertsIn s L) ⊆ L := by
  constructor
  · intro h s hs
    rcases Finset.eq_empty_or_nonempty (vertsIn s L) with hempty | hne
    · rw [hempty, PL.simp, Finset.coe_empty, convexHull_empty]
      exact empty_subset _
    · exact h s hs _ (vertsIn_subset s L) hne (vertsIn_subset_L s L)
  · intro h s hs t hts ht htL
    refine (convexHull_mono ?_).trans (h s hs)
    intro x hx
    exact Finset.mem_coe.mpr (mem_vertsIn.mpr ⟨hts (Finset.mem_coe.mp hx), htL hx⟩)

end

end Work.PL.SubdivFull
