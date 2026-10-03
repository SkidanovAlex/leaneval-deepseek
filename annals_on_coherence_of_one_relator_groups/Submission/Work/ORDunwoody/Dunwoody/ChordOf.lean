/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The chord matching of a face is the chord matching of the edge list of its walk in `T`

`Dunwoody/Chord.lean` pairs the visits of a face inside each fibre.  The pairing depends only on the
list of *labels* of the visits, which is the edge list of the walk in `T` obtained by reading the
word (`tWalkAux`, `Work.ORDunwoody.tWalkAux_edges`).  This file records that identity:

* `positionsOfLabelAux_map` / `chords_eq_chordsOf`: `chords` of a list of pattern points is
  `Chords.chordsOf` of its list of labels;
* `faceVisits_labels`: the labels of the visits of a face are the edges of its walk in `T`.

Consequently the nestedness theorem `Chords.chordsOf_nested` (chords of a closed walk in a forest
are nested) applies to the chords of a face, which is what `(N)` of `DESIGN_N13.md` §10.4 needs.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Chord
import Submission.Work.ORDunwoody.Chords.Basic
import Submission.Work.ORDunwoody.tWalkAux_edges
import Submission.Work.ORDunwoody.faceVisits_eq_faceAux
import Submission.Work.ORDunwoody.faceAux_eq_faceSteps

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

/-! ## `chords` only depends on the labels -/

/-- The two pairings agree. -/
theorem pairUp_apply_eq : ∀ l : List ℕ, pairUp l = Work.ORDunwoody.Chords.pairUp l
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
      simp only [pairUp, Work.ORDunwoody.Chords.pairUp]
      rw [pairUp_apply_eq t]

theorem pairUp_eq_chords : pairUp = Work.ORDunwoody.Chords.pairUp :=
  funext pairUp_apply_eq

/-- The positions of a value in a list of pattern points are the positions of that value in the
list of labels, for the abstract `posOfAux`. -/
theorem positionsOfLabelAux_map (l : List (MidV D)) (e : Sym2 V) (i : ℕ) :
    positionsOfLabelAux l e i =
      Work.ORDunwoody.Chords.posOfAux (l.map (MidV.label (D := D))) e i := by
  induction l generalizing i with
  | nil => rfl
  | cons m rest ih =>
      rw [List.map_cons, positionsOfLabelAux, Work.ORDunwoody.Chords.posOfAux_cons, ih]

theorem positionsOfLabel_map (l : List (MidV D)) (e : Sym2 V) :
    positionsOfLabel l e =
      Work.ORDunwoody.Chords.posOf (l.map (MidV.label (D := D))) e := by
  rw [positionsOfLabel, Work.ORDunwoody.Chords.posOf, positionsOfLabelAux_map]

/-- **The chords of a list of pattern points depend only on their labels.** -/
theorem chords_eq_chordsOf (l : List (MidV D)) :
    chords l = Work.ORDunwoody.Chords.chordsOf (l.map (MidV.label (D := D))) := by
  simp only [chords, labelSet, Work.ORDunwoody.Chords.chordsOf, positionsOfLabel_map,
    pairUp_eq_chords]

theorem IsChord_iff (l : List (MidV D)) (i j : ℕ) :
    IsChord l i j ↔ Work.ORDunwoody.Chords.IsChordOf (l.map (MidV.label (D := D))) i j := by
  unfold IsChord Work.ORDunwoody.Chords.IsChordOf
  rw [chords_eq_chordsOf]

/-! ## The labels of the visits are the edges of the walk in `T` -/

/-- **The labels of the visits of a face are the edges of the walk in `T`** obtained by reading the
word. -/
theorem faceVisits_labels (c : G) (w : List (Fin P.n × Bool)) :
    (faceVisits D c w).map (MidV.label (D := D)) = (tWalkAux D c w).edges := by
  have h1 : faceVisits D c w = (faceSteps D c w).filterMap DStep.mid? := by
    rw [faceVisits_eq_faceAux, faceAux_eq_faceSteps]
  rw [h1]
  rw [List.map_filterMap]
  rw [show (fun s : DStep D => (DStep.mid? s).map (MidV.label (D := D))) = DStep.edge?
    from funext (fun s => DStep.map_label_mid? s)]
  exact (tWalkAux_edges (D := D) c w).symm

/-- **The walk in `T` of a defining relator is a closed walk.** -/
noncomputable def tWalkClosed (r : {r : FreeGroup (Fin P.n) // r ∈ P.rel}) (c : G) :
    T.graph.Walk (colour D ((c, Sum.inl ()) : BaseV D)) (colour D ((c, Sum.inl ()) : BaseV D)) :=
  (tWalkAux D c (FreeGroup.toWord r.1)).copy rfl
    (congrArg (fun x => colour D ((x, Sum.inl ()) : BaseV D)) (endPt_toWord_eq (P := P) r.2 c))

theorem tWalkClosed_edges (r : {r : FreeGroup (Fin P.n) // r ∈ P.rel}) (c : G) :
    (tWalkClosed (D := D) r c).edges = (tWalkAux D c (FreeGroup.toWord r.1)).edges := by
  simp only [tWalkClosed, SimpleGraph.Walk.edges_copy]

end Work.ORDunwoody.Dunwoody
