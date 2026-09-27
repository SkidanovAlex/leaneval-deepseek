import Submission.Work.PL.SubdivFull.Defs
import Submission.Work.PL.SubdivFull.Basic
import Submission.Work.PL.SubdivFull.sd_full
import Submission.Work.PL.SubdivFull.sdIter_full

/-!
# Fullness of a union of closed faces after at least one subdivision

The main results of the area, in the `FullOn` form:

* `fullOn_sd` : if `L` is a union of closed faces of `K` then `L` is full in `sd K`;
* `fullOn_sdIter` : the same in `sdIter r K` for every `1 ≤ r`;
* `sd_simp_vertsIn` / `sdIter_simp_vertsIn` : the form used by the `E4` repair -- the vertices of a
  face of `sd K` (resp. `sdIter r K`, `1 ≤ r`) which lie in `L` span a simplex contained in `L`.

The raw-hypothesis statements of the lead's contract (`NOTES_LEAD_poincare_E4fix.md` §5) are
`Work.PL.SubdivFull.sd_full` and `Work.PL.SubdivFull.sdIter_full` (modules
`Submission.Work.PL.SubdivFull.sd_full`, `...sdIter_full`); the names `Work.PL.Subdiv.sd_full`,
`Work.PL.Subdiv.sdIter_full` of §5 itself are provided in `Submission.Work.PL.SubdivFull.Compat`.
-/

open Set Metric
open PL

namespace Work.PL.SubdivFull

noncomputable section

variable {N : ℕ}

/-- **A2, fullness at one subdivision** (`FullOn` form): a union of closed faces of `K` is full in
`sd K`. -/
theorem fullOn_sd {K : PL.Cx N} {L : Set (PL.E N)} (h : IsFaceUnion K L) :
    FullOn (Work.PL.Subdiv.sd K) L :=
  fun _s hs _t hts ht htL => sd_full h.1 h.2 hs hts ht htL

/-- **A2, fullness after at least one subdivision** (`FullOn` form). -/
theorem fullOn_sdIter {K : PL.Cx N} (hK : K.faces.Finite) {L : Set (PL.E N)}
    (h : IsFaceUnion K L) {r : ℕ} (hr : 1 ≤ r) : FullOn (Work.PL.Subdiv.sdIter r K hK) L :=
  fun _s hs _t hts ht htL => sdIter_full r K hK L h.1 h.2 hr hs hts ht htL

/-- The vertices of a face of `sdIter r K` (`1 ≤ r`) lying in a union of faces `L` of `K` span a
simplex contained in `L`. -/
theorem sdIter_simp_vertsIn {K : PL.Cx N} (hK : K.faces.Finite) {L : Set (PL.E N)}
    (h : IsFaceUnion K L) {r : ℕ} (hr : 1 ≤ r) {s : Finset (PL.E N)}
    (hs : s ∈ (Work.PL.Subdiv.sdIter r K hK).faces) : PL.simp (vertsIn s L) ⊆ L :=
  (fullOn_iff_filter _ _).mp (fullOn_sdIter hK h hr) s hs

/-- The vertices of a face of `sd K` lying in a union of faces `L` of `K` span a simplex contained
in `L`. -/
theorem sd_simp_vertsIn {K : PL.Cx N} {L : Set (PL.E N)} (h : IsFaceUnion K L)
    {s : Finset (PL.E N)} (hs : s ∈ (Work.PL.Subdiv.sd K).faces) : PL.simp (vertsIn s L) ⊆ L :=
  (fullOn_iff_filter _ _).mp (fullOn_sd h) s hs

/-- **The raw-hypothesis form of fullness without the nonemptiness side condition** (which is
automatic: the simplex on the empty vertex set is empty). -/
theorem sd_simp_of_subset_faces {K : PL.Cx N} {L : Set (PL.E N)} (h : IsFaceUnion K L)
    {s t : Finset (PL.E N)} (hs : s ∈ (Work.PL.Subdiv.sd K).faces) (hts : t ⊆ s)
    (htL : (↑t : Set (PL.E N)) ⊆ L) : PL.simp t ⊆ L := by
  rcases t.eq_empty_or_nonempty with rfl | hne
  · rw [PL.simp, Finset.coe_empty, convexHull_empty]
    exact empty_subset _
  · exact sd_full h.1 h.2 hs hts hne htL

/-- **The raw-hypothesis form of fullness after at least one subdivision, without the
nonemptiness side condition.**  This is the form the `E4` repair uses for `t = s ∩ Fzv`
(the frozen vertices of a fine face). -/
theorem sdIter_simp_of_subset_faces {K : PL.Cx N} (hK : K.faces.Finite) {L : Set (PL.E N)}
    (h : IsFaceUnion K L) {r : ℕ} (hr : 1 ≤ r) {s t : Finset (PL.E N)}
    (hs : s ∈ (Work.PL.Subdiv.sdIter r K hK).faces) (hts : t ⊆ s)
    (htL : (↑t : Set (PL.E N)) ⊆ L) : PL.simp t ⊆ L := by
  rcases t.eq_empty_or_nonempty with rfl | hne
  · rw [PL.simp, Finset.coe_empty, convexHull_empty]
    exact empty_subset _
  · exact sdIter_full r K hK L h.1 h.2 hr hs hts hne htL

end

end Work.PL.SubdivFull
