import Mathlib
import Submission.Work.PL.SubdivFull.Defs
import Submission.Work.PL.SubdivFull.Basic
import Submission.Work.PL.SubdivFull.sd_full

namespace Work.PL.SubdivFull

open Set Metric

/-!
# Fullness of a union of closed faces after `r ≥ 1` barycentric subdivisions

`IsFaceUnion.sdIter` (in `Basic`) says that a union `L` of closed faces of `K` is again a union of
closed faces of `sdIter n K`, and `sd_full` is the one-step fullness lemma.  Since
`sdIter (n + 1) K = sd (sdIter n K)` by definition, the general case with `1 ≤ r` is the one-step
case applied to `K' := sdIter n K` (`r = n + 1`), with the face-union hypotheses transported from
`K` to `sdIter n K`.
-/

theorem sdIter_full {N : ℕ} (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite) (L : Set (PL.E N))
    (hLs : L ⊆ K.space) (hL : ∀ x ∈ L, ∃ s ∈ K.faces, x ∈ PL.simp s ∧ PL.simp s ⊆ L) (hr : 1 ≤ r)
    {s : Finset (PL.E N)} (hs : s ∈ (Work.PL.Subdiv.sdIter r K hK).faces) {t : Finset (PL.E N)}
    (hts : t ⊆ s) (ht : t.Nonempty) (htL : (↑t : Set (PL.E N)) ⊆ L) : PL.simp t ⊆ L := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have hFU : IsFaceUnion (Work.PL.Subdiv.sdIter n K hK) L :=
    IsFaceUnion.sdIter ⟨hLs, hL⟩ hK n
  rw [Work.PL.Subdiv.sdIter_succ] at hs
  exact sd_full (K := Work.PL.Subdiv.sdIter n K hK) hFU.1 hFU.2 hs hts ht htL

end Work.PL.SubdivFull
