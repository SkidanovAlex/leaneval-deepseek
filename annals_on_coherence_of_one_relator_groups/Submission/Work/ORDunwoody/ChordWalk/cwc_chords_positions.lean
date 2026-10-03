/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The chords of a list of visits join *consecutive* visits of their fibre

`Dunwoody/Chord.lean` defines the chords of a list `l` of visits (i.e. of pattern points on the
boundary walk of a face of `Λ''`): for each fibre — each edge `e` of `T` occurring among the labels
of the visits — the occurrences of `e` are listed in the order of the walk
(`Dunwoody.positionsOfLabel l e`) and paired two at a time (`Dunwoody.pairUp`):

  `chords l = (labelSet l).flatMap (fun e => pairUp (positionsOfLabel l e))`.

This file proves the structural information about a chord that the region/track construction uses:
a chord `(p, q)` consists of **two visits of one fibre, and there is no visit of that fibre strictly
between them**.  Concretely, for `(p, q) ∈ chords l`:

* `p < q`, and both `p` and `q` are positions of `l`;
* there is an edge `e` of `T` with `l[p].label = l[q].label = e`;
* no intermediate position carries the label `e`.

The proof is elementary list combinatorics, and splits into two independent halves, each proved in
its own module:

* membership in `positionsOfLabel l e` is exactly "a position of `l` whose visit has label `e`"
  (`cwc_mem_positionsOfLabel_iff`), and the positions of a fibre are recorded in strictly
  increasing order (`cwc_positionsOfLabel_pairwise`);
* the entries of a pair produced by `pairUp` are entries of the list (`cwc_pairUp_mem`), and in a
  strictly increasing list the entries of such a pair are ordered with no element of the list
  between them (`cwc_pairUp_spec`).

The first half identifies the fibre of the chord and the labels of its two visits; the second half
turns the pairing into the ordering and the "nothing in between" statement.
-/
import Mathlib
import Submission.Work.ORDunwoody.ChordWalk.Defs
import Submission.Work.ORDunwoody.ChordWalk.cwc_pairUp_mem
import Submission.Work.ORDunwoody.ChordWalk.cwc_pairUp_spec
import Submission.Work.ORDunwoody.ChordWalk.cwc_mem_positionsOfLabel_iff
import Submission.Work.ORDunwoody.ChordWalk.cwc_positionsOfLabel_pairwise

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORDunwoody.ChordWalk

open Work.ORDunwoody.Dunwoody

/-- A position at which a visit of label `e` sits belongs to the fibre `e`.  This is the direction
of `cwc_mem_positionsOfLabel_iff` that takes only the label of the visit, the (automatic) length
bound being recovered from the fact that `l[j]?` is a `some`; it is what feeds an intermediate
position of `l` into `cwc_pairUp_spec`. -/
private lemma mem_positionsOfLabel_of_label {G : Type u} [Group G] {V : Type u}
    [MulAction G V] [DecidableEq V] {T : Work.ORDunwoody.GTree G V} {t₀ : V}
    {P : Work.ORDunwoody.FinPresentation G} {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}
    {l : List (Work.ORDunwoody.Dunwoody.MidV D)} {e : Sym2 V} {j : ℕ}
    (h : (l[j]?).map (Work.ORDunwoody.Dunwoody.MidV.label (D := D)) = some e) :
    j ∈ Work.ORDunwoody.Dunwoody.positionsOfLabel l e := by
  have hj : j < l.length := by
    obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.mp h
    exact (List.getElem?_eq_some_iff.mp hm).1
  exact (cwc_mem_positionsOfLabel_iff (D := D)).mpr ⟨hj, h⟩

theorem cwc_chords_positions {G : Type u} [Group G] {V : Type u}
    [MulAction G V] [DecidableEq V] {T : Work.ORDunwoody.GTree G V} {t₀ : V}
    {P : Work.ORDunwoody.FinPresentation G} {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}
    {l : List (Work.ORDunwoody.Dunwoody.MidV D)} {p q : ℕ}
    (h : (p, q) ∈ Work.ORDunwoody.Dunwoody.chords l) :
    p < q ∧ p < l.length ∧ q < l.length ∧
      ∃ e : Sym2 V, (l[p]?).map Work.ORDunwoody.Dunwoody.MidV.label = some e ∧
        (l[q]?).map Work.ORDunwoody.Dunwoody.MidV.label = some e ∧
        (∀ r : ℕ, p < r → r < q → (l[r]?).map Work.ORDunwoody.Dunwoody.MidV.label ≠ some e) := by
  -- unfold the chords: `(p, q)` is a pair of consecutive visits of one fibre `e`
  rw [Work.ORDunwoody.Dunwoody.chords] at h
  rcases List.mem_flatMap.mp h with ⟨e, -, hpq⟩
  obtain ⟨hp_mem, hq_mem⟩ :=
    cwc_pairUp_mem (Work.ORDunwoody.Dunwoody.positionsOfLabel l e) p q hpq
  -- both ends of the chord are visits of label `e`, hence are positions of `l`
  obtain ⟨hp_lt, hp_lab⟩ := (cwc_mem_positionsOfLabel_iff (D := D)).mp hp_mem
  obtain ⟨hq_lt, hq_lab⟩ := (cwc_mem_positionsOfLabel_iff (D := D)).mp hq_mem
  -- the pairing is that of the increasing enumeration of the fibre: `p < q`, nothing in between
  obtain ⟨hpq_lt, hbetween⟩ :=
    cwc_pairUp_spec (cwc_positionsOfLabel_pairwise (D := D)) hpq
  exact ⟨hpq_lt, hp_lt, hq_lt, e, hp_lab, hq_lab, fun r hpr hrq hr =>
    hbetween r (mem_positionsOfLabel_of_label hr) hpr hrq⟩

end Work.ORDunwoody.ChordWalk
