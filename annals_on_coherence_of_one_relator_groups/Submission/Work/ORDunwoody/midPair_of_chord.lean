/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# Two pattern points joined by a chord have the same pair of adjacent regions

This file proves `Work.ORDunwoody.midPair_of_chord`: the two endpoints of a chord of a face (see
`Dunwoody/Chord.lean` for `chords`) have the same `midPair`, i.e. the same unordered pair of
adjacent regions.

The mathematics.  Two visits `m`, `m'` of the boundary walk of a face that are joined by a chord
lie in the same fibre, and the chord separates the two arcs of the face that it glues: the arc
*ending* at `m` (arc index `p`) is glued to the arc *starting* at `m'` (arc index `q + 1`), and the
arc ending at `m'` (arc index `q`) to the arc starting at `m` (arc index `p + 1`).  Since
`RegionRel` relates old vertices whose arc indices lie in the same *piece*
(`Dunwoody/Piece.lean`), this identifies `Region.mk m.src` with the region of the old vertex of arc
index `q + 1` — which is `m'.src` or `m'.tgt`, depending on the direction in which the walk
traverses the cell of `m'` — and `Region.mk m.tgt` with the region of the other one.  Hence
`s(Region.mk m.src, Region.mk m.tgt) = s(Region.mk m'.src, Region.mk m'.tgt)`.

The bookkeeping relating the *visit index* `p` of `faceVisits` to the *arc indices* of the two old
vertices flanking the visit is `Work.ORDunwoody.faceTriples_arcIndex`, which is applied in
`visit_triple_data` below.  It supplies, for the triple `t` of `faceTriples` at position `p`
(whose pattern point is `m` and whose first and third components flank it):

* the arc indices `p` and `p + 1` of the two flanking old vertices;
* the `Sym2`-equality `s(t.1, t.2.2) = s(m.src, m.tgt)`, i.e. the two flanking old vertices are
  exactly the two ends of `m`'s cell, in some order.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Track
import Submission.Work.ORDunwoody.Dunwoody.Piece
import Submission.Work.ORDunwoody.Dunwoody.Region
import Submission.Work.ORDunwoody.label_of_chord
import Submission.Work.ORDunwoody.faceTriples_arcIndex

set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Cayley
open scoped Sym2

/-! ## The data attached to a visit of a face -/

/-- **The data attached to a visit of a face.**  For a visit `m` at position `p` of the boundary
walk of the face `(c, w)` there is a triple `t` of `faceTriples`, sitting at position `p`, whose
pattern point is `m`, which records the pair of adjacent regions of `m` as
`s(Region.mk t.1, Region.mk t.2.2)`, and whose two old vertices have arc indices `p` and `p + 1`.

The first and third components of `t` are the old vertices immediately before and after `m` in the
walk, so they are the two ends of `m`'s cell in some order
(`Work.ORDunwoody.faceTriples_arcIndex`), which is why the `Sym2`-pair `s(t.1, t.2.2)` is the pair
of regions adjacent to `m`. -/
private theorem visit_triple_data {G : Type u} [Group G] {V : Type u} [MulAction G V]
    [DecidableEq V] {T : GTree G V} {t₀ : V} {P : FinPresentation G} {D : Cayley.GeoData T t₀ P}
    (c : G) (w : List (Fin P.n × Bool)) {p : ℕ} {m : Dunwoody.MidV D}
    (hm : (Dunwoody.faceVisits D c w)[p]? = some m) :
    ∃ t : Dunwoody.BaseV D × Dunwoody.MidV D × Dunwoody.BaseV D,
      (Dunwoody.faceTriples D c w)[p]? = some t ∧
      Dunwoody.midPair m = s(Dunwoody.Region.mk D t.1, Dunwoody.Region.mk D t.2.2) ∧
      (t.1, p) ∈ Dunwoody.arcIndex (Dunwoody.faceWalk D c w) ∧
      (t.2.2, p + 1) ∈ Dunwoody.arcIndex (Dunwoody.faceWalk D c w) := by
  -- the triple sitting at position `p`
  have hmap := hm
  rw [show Dunwoody.faceVisits D c w
        = (Dunwoody.faceTriples D c w).map (fun t => t.2.1) from rfl, List.getElem?_map] at hmap
  obtain ⟨t, ht, htm⟩ := Option.map_eq_some_iff.mp hmap
  -- the arc indices of the two flanking old vertices, and that they flank `m`
  obtain ⟨hu, hv, hflank⟩ := faceTriples_arcIndex (D := D) c w ht
  rw [htm] at hflank
  have hor : (m.src = t.1 ∧ m.tgt = t.2.2) ∨ (m.src = t.2.2 ∧ m.tgt = t.1) := by
    rcases Sym2.eq_iff.mp hflank with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h2.symm, h1.symm⟩
  have hmid : Dunwoody.midPair m = s(Dunwoody.Region.mk D t.1, Dunwoody.Region.mk D t.2.2) := by
    rw [Dunwoody.midPair]
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Sym2.eq_swap]
  exact ⟨t, ht, hmid, hu, hv⟩

/-! ## The main statement -/

theorem midPair_of_chord {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}
    (r : {r : FreeGroup (Fin P.n) // r ∈ P.rel}) (c : G) {p q : ℕ}
    (h : (p, q) ∈ Work.ORDunwoody.Dunwoody.chords
      (Work.ORDunwoody.Dunwoody.faceVisits D c (FreeGroup.toWord r.1)))
    {m m' : Work.ORDunwoody.Dunwoody.MidV D}
    (hm : (Work.ORDunwoody.Dunwoody.faceVisits D c (FreeGroup.toWord r.1))[p]? = some m)
    (hm' : (Work.ORDunwoody.Dunwoody.faceVisits D c (FreeGroup.toWord r.1))[q]? = some m') :
    Work.ORDunwoody.Dunwoody.midPair m = Work.ORDunwoody.Dunwoody.midPair m' := by
  obtain ⟨t, -, hmid, hu, hv⟩ := visit_triple_data (D := D) c (FreeGroup.toWord r.1) hm
  obtain ⟨t', -, hmid', hu', hv'⟩ := visit_triple_data (D := D) c (FreeGroup.toWord r.1) hm'
  obtain ⟨hpc, hqc⟩ := Dunwoody.pieceRel_of_chord h
  -- the two arcs separated by the chord lie in the same piece, hence their vertices in the same
  -- region: the arc ending at `m` (index `p`) with the arc starting at `m'` (index `q + 1`), and
  -- the arc ending at `m'` (index `q`) with the arc starting at `m` (index `p + 1`)
  have E1 : Dunwoody.Region.mk D t.1 = Dunwoody.Region.mk D t'.2.2 :=
    Dunwoody.Region.mk_eq_mk (Or.inr ⟨r, c, p, q + 1, hu, hv', hpc⟩)
  have E2 : Dunwoody.Region.mk D t.2.2 = Dunwoody.Region.mk D t'.1 :=
    (Dunwoody.Region.mk_eq_mk (Or.inr ⟨r, c, q, p + 1, hu', hv, hqc⟩)).symm
  calc Work.ORDunwoody.Dunwoody.midPair m
      = s(Dunwoody.Region.mk D t.1, Dunwoody.Region.mk D t.2.2) := hmid
    _ = s(Dunwoody.Region.mk D t'.2.2, Dunwoody.Region.mk D t.2.2) := by rw [E1]
    _ = s(Dunwoody.Region.mk D t'.2.2, Dunwoody.Region.mk D t'.1) := by rw [E2]
    _ = s(Dunwoody.Region.mk D t'.1, Dunwoody.Region.mk D t'.2.2) := Sym2.eq_swap
    _ = Work.ORDunwoody.Dunwoody.midPair m' := hmid'.symm

end Work.ORDunwoody
