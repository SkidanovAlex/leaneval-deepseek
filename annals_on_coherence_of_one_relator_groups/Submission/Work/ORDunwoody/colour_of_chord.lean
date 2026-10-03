/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# `colour_of_chord`: the two visits of a chord traverse their edge in opposite directions

`Dunwoody/Chord.lean` pairs the visits of the boundary walk of a face inside each *fibre* (each
label `Sym2 V`), the 1st visit of a fibre with the 2nd, the 3rd with the 4th, and so on.  This
file proves the geometric content of that pairing:

> if the visits at positions `p` and `q` of the walk are paired by a chord, then the arc *ending*
> at visit `p` and the arc *starting* at visit `q` have the **same colour** — that is, the two
> visits traverse the edge of `T` they label in *opposite* directions.

The proof has three parts.

* **The walk in `T`.**  Reading the colours of the visits in order gives a walk in `T`
  (`visitTgt`): the two old vertices on either side of a visit are the two ends of the edge of `T`
  the visit labels (`faceTriples_good`, from `faceTriples_arcIndex` and `cell_label_eq_colour`),
  and consecutive visits have agreeing colours where they meet
  (`Work.ORDunwoody.ChordWalk.cwc_faceTriples_colshare`, a consequence of `colour_arcIndex`).

* **Opposite directions.**  If `p < q` are *consecutive* visits with the same label `e` (which is
  exactly what a chord gives), then the part of the walk strictly between them crosses no edge
  labelled `e`.  A walk in a forest that avoids an edge cannot pass from one side of it to the
  other (`Work.ORDunwoody.ChordWalk.cwc_chain_avoids_edge`); hence the walk is still at the
  endpoint at which the `p`-th visit arrived when the `q`-th visit starts, i.e. the two visits
  cross `e` in opposite directions (`triples_crux`).

* **Assembly.**  `Work.ORDunwoody.ChordWalk.cwc_chords_positions` turns a chord into the two
  consecutive visits of its fibre; `faceTriples_arcIndex` identifies the arcs with the flanks of
  the visits and `colour_arcIndex` shows that all the old vertices of an arc have the same
  colour.
-/
import Mathlib
import Submission.Work.ORDunwoody.faceTriples_arcIndex
import Submission.Work.ORDunwoody.colour_arcIndex
import Submission.Work.ORDunwoody.ChordWalk.StepDefs
import Submission.Work.ORDunwoody.ChordWalk.cwc_chain_avoids_edge
import Submission.Work.ORDunwoody.ChordWalk.cwc_chords_positions
import Submission.Work.ORDunwoody.ChordWalk.cwc_faceTriples_colshare

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Dunwoody Work.ORDunwoody.Cayley
open scoped Sym2

section Helpers

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-- The colours of the targets of the visits of a face, in order: the vertex sequence of the walk
in `T` induced by the face. -/
private def visitTgt (c : G) (w : List (Fin P.n × Bool)) : List V :=
  (faceTriples D c w).map (fun t => colour D t.2.2)

/-- The `k`-th entry of the walk `visitTgt`. -/
private theorem visitTgt_getElem (c : G) (w : List (Fin P.n × Bool)) {k : ℕ}
    (hk : k < (faceTriples D c w).length) :
    (visitTgt (D := D) c w)[k]? = some (colour D (faceTriples D c w)[k].2.2) := by
  unfold visitTgt
  rw [List.getElem?_map, List.getElem?_eq_getElem hk]
  rfl

/-- Each entry of `faceTriples` records a genuine edge of `T`: the two old vertices on either side
of the visit have adjacent colours, and the `Sym2`-pair of those colours is the visit's label. -/
private theorem faceTriples_good (c : G) (w : List (Fin P.n × Bool)) :
    ∀ (k : ℕ) (a : BaseV D) (m : MidV D) (b : BaseV D),
      (faceTriples D c w)[k]? = some (a, m, b) →
        T.graph.Adj (colour D a) (colour D b) ∧ s(colour D a, colour D b) = m.label := by
  intro k a m b h
  obtain ⟨-, -, hsym⟩ := faceTriples_arcIndex c w h
  have h1 : s(colour D a, colour D b) = m.label := by
    rcases Sym2.eq_iff.mp hsym with hc | hc
    · rw [hc.1, hc.2]; exact (MidV.label_eq_colour m).symm
    · rw [hc.1, hc.2, Sym2.eq_swap]; exact (MidV.label_eq_colour m).symm
  refine ⟨?_, h1⟩
  have hmem : m.label ∈ T.graph.edgeSet := by
    have h2 := Cell.label_mem_edgeSet (D := D) (MidV.cell m)
    rwa [Cell.label_eq_MidV_label, MidV.cell_mid] at h2
  rw [← h1] at hmem
  exact (SimpleGraph.mem_edgeSet T.graph).mp hmem

/-- **The two visits of a chord traverse their edge in opposite directions.**  If the visits at
positions `p < q` of the boundary walk of a face label the same edge of `T`, and no visit strictly
between them does, then the colour of the target of the `p`-th visit equals the colour of the
source of the `q`-th visit. -/
private theorem triples_crux (c : G) (w : List (Fin P.n × Bool))
    (hcolshare : ∀ (k : ℕ) (a : BaseV D) (m : MidV D) (b : BaseV D)
      (a' : BaseV D) (m' : MidV D) (b' : BaseV D),
      (faceTriples D c w)[k]? = some (a, m, b) →
        (faceTriples D c w)[k + 1]? = some (a', m', b') → colour D b = colour D a')
    {p q : ℕ} {a bp a' bp' : BaseV D} {mp mq : MidV D}
    (hp : (faceTriples D c w)[p]? = some (a, mp, bp))
    (hq : (faceTriples D c w)[q]? = some (a', mq, bp'))
    (hlabel : mp.label = mq.label) (hpq : p < q)
    (havoid : ∀ (r : ℕ) (a'' : BaseV D) (m'' : MidV D) (b'' : BaseV D),
      p < r → r < q → (faceTriples D c w)[r]? = some (a'', m'', b'') → m''.label ≠ mp.label) :
    colour D a = colour D bp' := by
  classical
  obtain ⟨hg1, hl1⟩ := faceTriples_good (D := D) c w p a mp bp hp
  obtain ⟨hg2, hl2⟩ := faceTriples_good (D := D) c w q a' mq bp' hq
  obtain ⟨hqlt, -⟩ := List.getElem?_eq_some_iff.mp hq
  -- The walk in `T` from the target of the `p`-th visit to the source of the `q`-th visit.
  have hbc : colour D bp = colour D a' := by
    have hwalk : (visitTgt (D := D) c w).IsChain (fun x y => x = y ∨ T.graph.Adj x y) := by
      unfold visitTgt
      rw [List.isChain_map, List.isChain_iff_getElem]
      intro i hi
      have hi1 : i < (faceTriples D c w).length := by omega
      have hcs : colour D (faceTriples D c w)[i].2.2 = colour D (faceTriples D c w)[i+1].1 :=
        hcolshare i (faceTriples D c w)[i].1 (faceTriples D c w)[i].2.1
          (faceTriples D c w)[i].2.2 (faceTriples D c w)[i+1].1 (faceTriples D c w)[i+1].2.1
          (faceTriples D c w)[i+1].2.2
          (by rw [List.getElem?_eq_getElem hi1])
          (by rw [List.getElem?_eq_getElem hi])
      have hg : T.graph.Adj (colour D (faceTriples D c w)[i+1].1)
          (colour D (faceTriples D c w)[i+1].2.2) :=
        (faceTriples_good (D := D) c w (i+1) (faceTriples D c w)[i+1].1
          (faceTriples D c w)[i+1].2.1 (faceTriples D c w)[i+1].2.2
          (by rw [List.getElem?_eq_getElem hi])).1
      rw [hcs]
      exact Or.inr hg
    have hchain : ((visitTgt (D := D) c w).drop p |>.take (q - p)).IsChain
        (fun x y => x = y ∨ T.graph.Adj x y) := (hwalk.drop p).take (q - p)
    have heq : s(colour D a, colour D bp) = s(colour D a', colour D bp') := by
      calc s(colour D a, colour D bp) = mp.label := hl1
        _ = mq.label := hlabel
        _ = s(colour D a', colour D bp') := hl2.symm
    have hhead : ((visitTgt (D := D) c w).drop p |>.take (q - p)).head? =
        some (colour D bp) := by
      rw [List.head?_take, if_neg (by omega : ¬ (q - p = 0)), List.head?_drop]
      unfold visitTgt
      rw [List.getElem?_map, hp]
      rfl
    have hlast : ((visitTgt (D := D) c w).drop p |>.take (q - p)).getLast? =
        some (colour D a') := by
      have hmid : (visitTgt (D := D) c w)[q - 1]? = some (colour D a') := by
        rw [visitTgt_getElem c w (by omega : q - 1 < (faceTriples D c w).length)]
        congr 1
        have hcs : colour D (faceTriples D c w)[q - 1].2.2 = colour D a' :=
          hcolshare (q - 1) (faceTriples D c w)[q - 1].1 (faceTriples D c w)[q - 1].2.1
            (faceTriples D c w)[q - 1].2.2 a' mq bp'
            (by rw [List.getElem?_eq_getElem (by omega : q - 1 < (faceTriples D c w).length)])
            (by rw [show q - 1 + 1 = q from by omega]; exact hq)
        exact hcs
      rw [List.getLast?_take, if_neg (by omega : ¬ (q - p = 0)), List.getElem?_drop]
      rw [show p + (q - p - 1) = q - 1 from by omega]
      rw [hmid, Option.some_or]
    have havoid' : ∀ (i : ℕ) (x y : V),
        ((visitTgt (D := D) c w).drop p |>.take (q - p))[i]? = some x →
        ((visitTgt (D := D) c w).drop p |>.take (q - p))[i + 1]? = some y → x ≠ y →
        s(x, y) ≠ s(colour D a, colour D bp) := by
      intro i x y hx hy _
      have hi : i < q - p := by
        by_contra hcon
        rw [List.getElem?_take, if_neg hcon] at hx
        exact absurd hx (by simp)
      have hi1 : i + 1 < q - p := by
        by_contra hcon
        rw [List.getElem?_take, if_neg hcon] at hy
        exact absurd hy (by simp)
      have hb1 : p + i < (faceTriples D c w).length := by omega
      have hb2 : p + i + 1 < (faceTriples D c w).length := by omega
      rw [List.getElem?_take, if_pos hi, List.getElem?_drop] at hx
      rw [List.getElem?_take, if_pos hi1, List.getElem?_drop] at hy
      rw [show p + (i + 1) = p + i + 1 from by omega] at hy
      rw [visitTgt_getElem c w (k := p + i) hb1] at hx
      rw [visitTgt_getElem c w (k := p + i + 1) hb2] at hy
      have hx' : colour D (faceTriples D c w)[p + i].2.2 = x := Option.some.inj hx
      have hy' : colour D (faceTriples D c w)[p + i + 1].2.2 = y := Option.some.inj hy
      rw [← hx', ← hy']
      have hcs : colour D (faceTriples D c w)[p + i].2.2 =
          colour D (faceTriples D c w)[p + i + 1].1 :=
        hcolshare (p + i) (faceTriples D c w)[p + i].1 (faceTriples D c w)[p + i].2.1
          (faceTriples D c w)[p + i].2.2 (faceTriples D c w)[p + i + 1].1
          (faceTriples D c w)[p + i + 1].2.1 (faceTriples D c w)[p + i + 1].2.2
          (by rw [List.getElem?_eq_getElem hb1])
          (by rw [List.getElem?_eq_getElem hb2])
      rw [hcs]
      intro hcontra
      have hgl : s(colour D (faceTriples D c w)[p + i + 1].1,
            colour D (faceTriples D c w)[p + i + 1].2.2) =
          (faceTriples D c w)[p + i + 1].2.1.label :=
        (faceTriples_good (D := D) c w (p + i + 1) (faceTriples D c w)[p + i + 1].1
          (faceTriples D c w)[p + i + 1].2.1 (faceTriples D c w)[p + i + 1].2.2
          (by rw [List.getElem?_eq_getElem hb2])).2
      rw [hgl, hl1] at hcontra
      exact havoid (p + i + 1) (faceTriples D c w)[p + i + 1].1 (faceTriples D c w)[p + i + 1].2.1
        (faceTriples D c w)[p + i + 1].2.2 (by omega) (by omega)
        (by rw [List.getElem?_eq_getElem hb2]) hcontra
    exact ChordWalk.cwc_chain_avoids_edge T.graph T.isTree.isAcyclic hg1 hg2 heq
      ((visitTgt (D := D) c w).drop p |>.take (q - p)) hchain hhead hlast havoid'
  -- The `p`-th visit leaves `colour bp = colour a'` and arrives at `colour a`; the `q`-th visit
  -- leaves `colour a'` and arrives at `colour bp'`; since the two labels agree, the other two
  -- endpoints agree as well.
  have hs : s(colour D a, colour D bp) = s(colour D bp, colour D bp') := by
    calc s(colour D a, colour D bp) = mp.label := hl1
      _ = mq.label := hlabel
      _ = s(colour D a', colour D bp') := hl2.symm
      _ = s(colour D bp, colour D bp') := by rw [← hbc]
  rcases Sym2.eq_iff.mp hs with hcase | hcase
  · exact absurd (hcase.1 ▸ hg1) (T.adj_self (colour D bp))
  · exact hcase.1

/-- The `k`-th visit of a face, as the middle entry of the `k`-th element of `faceTriples`. -/
private theorem faceVisits_getElem (c : G) (w : List (Fin P.n × Bool)) {k : ℕ}
    (hk : k < (faceTriples D c w).length) :
    (faceVisits D c w)[k]? = some (faceTriples D c w)[k].2.1 := by
  simp only [faceVisits, List.getElem?_map, List.getElem?_eq_getElem hk]
  rfl

end Helpers

theorem colour_of_chord {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (c : G) (w : List (Fin P.n × Bool))
    {p q : ℕ} (h : (p, q) ∈ Work.ORDunwoody.Dunwoody.chords
      (Work.ORDunwoody.Dunwoody.faceVisits D c w))
    {u v : Work.ORDunwoody.Dunwoody.BaseV D}
    (hu : (u, p) ∈ Work.ORDunwoody.Dunwoody.arcIndex (Work.ORDunwoody.Dunwoody.faceWalk D c w))
    (hv : (v, q + 1) ∈ Work.ORDunwoody.Dunwoody.arcIndex (Work.ORDunwoody.Dunwoody.faceWalk D c w)) :
    Work.ORDunwoody.Dunwoody.colour D u = Work.ORDunwoody.Dunwoody.colour D v := by
  classical
  obtain ⟨hpq, hplt, hqlt, e, he1, he2, havoid0⟩ := ChordWalk.cwc_chords_positions h
  have hlenv : (faceVisits D c w).length = (faceTriples D c w).length := by
    simp only [faceVisits, List.length_map]
  have hlenp : p < (faceTriples D c w).length := by omega
  have hlenq : q < (faceTriples D c w).length := by omega
  have hp : (faceTriples D c w)[p]? =
      some ((faceTriples D c w)[p].1, (faceTriples D c w)[p].2.1, (faceTriples D c w)[p].2.2) :=
    List.getElem?_eq_getElem hlenp
  have hq : (faceTriples D c w)[q]? =
      some ((faceTriples D c w)[q].1, (faceTriples D c w)[q].2.1, (faceTriples D c w)[q].2.2) :=
    List.getElem?_eq_getElem hlenq
  have hpv : (faceVisits D c w)[p]? = some (faceTriples D c w)[p].2.1 :=
    faceVisits_getElem c w hlenp
  have hqv : (faceVisits D c w)[q]? = some (faceTriples D c w)[q].2.1 :=
    faceVisits_getElem c w hlenq
  have hlabp : (faceTriples D c w)[p].2.1.label = e := by
    have h' := he1
    rw [hpv] at h'
    simpa using h'
  have hlabq : (faceTriples D c w)[q].2.1.label = e := by
    have h' := he2
    rw [hqv] at h'
    simpa using h'
  have hlabel : (faceTriples D c w)[p].2.1.label = (faceTriples D c w)[q].2.1.label := by
    rw [hlabp, hlabq]
  have havoid : ∀ (r : ℕ) (a'' : BaseV D) (m'' : MidV D) (b'' : BaseV D),
      p < r → r < q → (faceTriples D c w)[r]? = some (a'', m'', b'') →
        m''.label ≠ (faceTriples D c w)[p].2.1.label := by
    intro r a'' m'' b'' hpr hrq hr
    have hrv : (faceVisits D c w)[r]? = some m'' := by
      rw [faceVisits, List.getElem?_map, hr]
      rfl
    have hne := havoid0 r hpr hrq
    intro hc
    apply hne
    rw [hrv]
    rw [show Option.map MidV.label (some m'') = some (m''.label) from rfl, hc, hlabp]
  have hcrux : colour D (faceTriples D c w)[p].1 = colour D (faceTriples D c w)[q].2.2 :=
    triples_crux c w
      (fun k a m b a' m' b' h h' => ChordWalk.cwc_faceTriples_colshare (D := D) c w h h')
      hp hq hlabel hpq havoid
  have hAp : ((faceTriples D c w)[p].1, p) ∈ arcIndex (faceWalk D c w) :=
    (faceTriples_arcIndex c w hp).1
  have hBq : ((faceTriples D c w)[q].2.2, q + 1) ∈ arcIndex (faceWalk D c w) :=
    (faceTriples_arcIndex c w hq).2.1
  rw [colour_arcIndex c w hu hAp, colour_arcIndex c w hv hBq]
  exact hcrux

end Work.ORDunwoody
