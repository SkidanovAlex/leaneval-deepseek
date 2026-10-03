/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# Nestedness of the chords of a face

`Chords/chordsOf_nested` proves that the chord matching of the edge list of a *closed walk in a
forest* is nested.  By `Dunwoody/ChordOf.lean` the chord matching of the visits of a face is the
chord matching of the edge list of its walk in `T` (`tWalkClosed`), so nestedness holds for the
chords of every face.  This is the input `(N)` of `DESIGN_N13.md` §10.4.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.ChordOf
import Submission.Work.ORDunwoody.Chords.chordsOf_nested

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley
open scoped Sym2

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-- **The chords of a face are nested**: every visit strictly between the two ends of a chord is
paired (by the chord matching of the face) with another visit strictly between them. -/
theorem chords_nested_face (r : {r : FreeGroup (Fin P.n) // r ∈ P.rel}) (c : G)
    {p q : ℕ} (h : (p, q) ∈ chords (faceVisits D c (FreeGroup.toWord r.1))) (hpq : p < q)
    {t : ℕ} (hpt : p < t) (htq : t < q) :
    ∃ t', p < t' ∧ t' < q ∧ IsChord (faceVisits D c (FreeGroup.toWord r.1)) t t' := by
  have htr : (faceVisits D c (FreeGroup.toWord r.1)).map (MidV.label (D := D)) =
      (tWalkClosed (D := D) r c).edges := by
    rw [faceVisits_labels, tWalkClosed_edges]
  have h' : (p, q) ∈ Work.ORDunwoody.Chords.chordsOf (tWalkClosed (D := D) r c).edges := by
    rw [← htr, ← chords_eq_chordsOf]
    exact h
  obtain ⟨t', h1, h2, h3⟩ :=
    Work.ORDunwoody.Chords.chordsOf_nested T.isTree.2 (tWalkClosed (D := D) r c) h' hpq hpt htq
  refine ⟨t', h1, h2, ?_⟩
  rw [IsChord_iff, htr]
  exact h3

end Work.ORDunwoody.Dunwoody
