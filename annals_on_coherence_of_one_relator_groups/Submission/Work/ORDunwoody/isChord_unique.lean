/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The chord relation of a face is a *matching*

`Dunwoody.chords l` (`Dunwoody/Chord.lean`) is the list of chords of a list of visits: for every
fibre — every edge `e` of `T` occurring among the labels of `l` — the visits of that fibre are
listed in the order of the walk (`Dunwoody.positionsOfLabel l e`) and paired two at a time
(`Dunwoody.pairUp`).  The *chord relation* `Dunwoody.IsChord l t u` holds when `t` and `u` are the
two visits of one such pair (in either order).

This file proves that this relation is (the graph of) a **function**: a visit has at most one
partner.  Equivalently, the list of chords of `chords l` is a matching of the positions of `l`.
This is hypothesis `(U)` of `DESIGN_N13.md` §9.3: it lets `sum_eq_zero_of_partner` split a set of
positions that is a union of chords into genuine pairs.

The proof has two ingredients, both proved in their own modules:

* `ChordWalk.cwc_pairUp_matching` — on a **strictly increasing** list `L`, `pairUp L` pairs
  entries in disjoint consecutive blocks `(L₀,L₁), (L₂,L₃), …`, so a first coordinate determines
  its pair, a second coordinate determines its pair, and no pair is the "swap" of another.  (The
  hypothesis "strictly increasing" is exactly the non-degeneracy needed: `pairUp [0,0,0,1]`
  contains both `(0,0)` and `(0,1)`.)
* `ChordWalk.cwc_chord_fibre` — a chord `(p, q)` of `chords l` comes with a fibre `e` such that
  `(p, q) ∈ pairUp (positionsOfLabel l e)` and `l[p].label = l[q].label = e`.

Since the positions of one fibre are strictly increasing
(`ChordWalk.cwc_positionsOfLabel_pairwise`) and the fibre of a chord is determined by the label of
its first (or second) coordinate, a visit `t` engages only the fibre `label (l[t])`, and inside
that fibre the pairing is a matching.  That settles the four cases of
`IsChord l t u = (t,u) ∈ chords l ∨ (u,t) ∈ chords l`.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Chord
import Submission.Work.ORDunwoody.Chords.Basic
import Submission.Work.ORDunwoody.ChordWalk.cwc_chords_positions
import Submission.Work.ORDunwoody.ChordWalk.cwc_mem_positionsOfLabel_iff
import Submission.Work.ORDunwoody.ChordWalk.cwc_positionsOfLabel_pairwise
import Submission.Work.ORDunwoody.ChordWalk.cwc_pairUp_mem
import Submission.Work.ORDunwoody.ChordWalk.cwc_pairUp_matching
import Submission.Work.ORDunwoody.ChordWalk.cwc_chord_fibre

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORDunwoody

universe u

theorem isChord_unique {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}
    {l : List (Work.ORDunwoody.Dunwoody.MidV D)} {t u v : ℕ}
    (htu : Work.ORDunwoody.Dunwoody.IsChord l t u)
    (htv : Work.ORDunwoody.Dunwoody.IsChord l t v) : u = v := by
  rcases htu with htu | htu <;> rcases htv with htv | htv
  · -- `(t, u)` and `(t, v)` are chords of one fibre: their right ends coincide
    obtain ⟨e, hu, ht1, -⟩ := ChordWalk.cwc_chord_fibre htu
    obtain ⟨f, hv, ht2, -⟩ := ChordWalk.cwc_chord_fibre htv
    have hef : e = f := Option.some.inj (ht1.symm.trans ht2)
    subst hef
    exact (ChordWalk.cwc_pairUp_matching
      (ChordWalk.cwc_positionsOfLabel_pairwise (D := D) (l := l) (e := e))).1 t u v hu hv
  · -- `(t, u)` and `(v, t)` are chords of one fibre: impossible, the pairing is not swapped
    obtain ⟨e, hu, ht1, -⟩ := ChordWalk.cwc_chord_fibre htu
    obtain ⟨f, hv, -, ht2⟩ := ChordWalk.cwc_chord_fibre htv
    have hef : e = f := Option.some.inj (ht1.symm.trans ht2)
    subst hef
    exact ((ChordWalk.cwc_pairUp_matching
      (ChordWalk.cwc_positionsOfLabel_pairwise (D := D) (l := l) (e := e))).2.2 v t u hv hu).elim
  · -- `(u, t)` and `(t, v)`: again impossible, the pairing is not swapped
    obtain ⟨e, hu, -, ht1⟩ := ChordWalk.cwc_chord_fibre htu
    obtain ⟨f, hv, ht2, -⟩ := ChordWalk.cwc_chord_fibre htv
    have hef : e = f := Option.some.inj (ht1.symm.trans ht2)
    subst hef
    exact ((ChordWalk.cwc_pairUp_matching
      (ChordWalk.cwc_positionsOfLabel_pairwise (D := D) (l := l) (e := e))).2.2 u t v hu hv).elim
  · -- `(u, t)` and `(v, t)` are chords of one fibre: their left ends coincide
    obtain ⟨e, hu, -, ht1⟩ := ChordWalk.cwc_chord_fibre htu
    obtain ⟨f, hv, -, ht2⟩ := ChordWalk.cwc_chord_fibre htv
    have hef : e = f := Option.some.inj (ht1.symm.trans ht2)
    subst hef
    exact (ChordWalk.cwc_pairUp_matching
      (ChordWalk.cwc_positionsOfLabel_pairwise (D := D) (l := l) (e := e))).2.1 u t v hu hv

end Work.ORDunwoody
