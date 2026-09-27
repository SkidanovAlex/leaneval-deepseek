import Submission.Work.PL.SubdivFull.sd_full
import Submission.Work.PL.SubdivFull.sdIter_full

/-!
# Compatibility names for the §5 contract

`Submission/Work/NOTES_LEAD_poincare_E4fix.md` §5 asks for the two fullness lemmas under the names
`Work.PL.Subdiv.sd_full` and `Work.PL.Subdiv.sdIter_full` (the `PL/Subdiv` area is delivered and
frozen, so they are re-exported here under those names).  The definitions, proofs and primary
names all live in `Work.PL.SubdivFull`:

* `Work.PL.SubdivFull.sd_full`  (module `Submission.Work.PL.SubdivFull.sd_full`)
* `Work.PL.SubdivFull.sdIter_full` (module `Submission.Work.PL.SubdivFull.sdIter_full`)

So `full := fun r K hK L hL hr s hs t hts hne htL =>
Work.PL.Subdiv.sdIter_full r K hK L hL.1 hL.2 hr hs hts hne htL` (with `hL : IsSubSp K L`, whose
two components are exactly the `hLs` / `hL` hypotheses below) works verbatim once this module is
imported.  If you prefer to define your own alias, import the two modules above and skip this one.
-/

open Set Metric

namespace Work.PL.Subdiv

/-- The §5 name for `Work.PL.SubdivFull.sd_full`: a union of closed faces `L` of `K` is full in
`sd K`. -/
theorem sd_full {N : ℕ} {K : PL.Cx N} {L : Set (PL.E N)} (hLs : L ⊆ K.space)
    (hL : ∀ x ∈ L, ∃ s ∈ K.faces, x ∈ PL.simp s ∧ PL.simp s ⊆ L)
    {s : Finset (PL.E N)} (hs : s ∈ (Work.PL.Subdiv.sd K).faces) {t : Finset (PL.E N)}
    (hts : t ⊆ s) (ht : t.Nonempty) (htL : (↑t : Set (PL.E N)) ⊆ L) : PL.simp t ⊆ L :=
  Work.PL.SubdivFull.sd_full hLs hL hs hts ht htL

/-- The §5 name for `Work.PL.SubdivFull.sdIter_full`: a union of closed faces `L` of `K` is full in
`sdIter r K` for every `1 ≤ r`. -/
theorem sdIter_full {N : ℕ} (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite) (L : Set (PL.E N))
    (hLs : L ⊆ K.space) (hL : ∀ x ∈ L, ∃ s ∈ K.faces, x ∈ PL.simp s ∧ PL.simp s ⊆ L) (hr : 1 ≤ r)
    {s : Finset (PL.E N)} (hs : s ∈ (Work.PL.Subdiv.sdIter r K hK).faces) {t : Finset (PL.E N)}
    (hts : t ⊆ s) (ht : t.Nonempty) (htL : (↑t : Set (PL.E N)) ⊆ L) : PL.simp t ⊆ L :=
  Work.PL.SubdivFull.sdIter_full r K hK L hLs hL hr hs hts ht htL

end Work.PL.Subdiv
