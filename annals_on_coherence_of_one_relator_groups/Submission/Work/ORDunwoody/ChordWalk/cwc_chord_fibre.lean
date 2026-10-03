import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Chord
import Submission.Work.ORDunwoody.ChordWalk.cwc_pairUp_mem
import Submission.Work.ORDunwoody.ChordWalk.cwc_mem_positionsOfLabel_iff

universe u

namespace Work.ORDunwoody.ChordWalk

theorem cwc_chord_fibre {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} {l : List (Work.ORDunwoody.Dunwoody.MidV D)}
    {p q : ℕ} (h : (p, q) ∈ Work.ORDunwoody.Dunwoody.chords l) :
    ∃ e : Sym2 V, (p, q) ∈ Work.ORDunwoody.Dunwoody.pairUp
        (Work.ORDunwoody.Dunwoody.positionsOfLabel l e) ∧
      (l[p]?).map (Work.ORDunwoody.Dunwoody.MidV.label (D := D)) = some e ∧
      (l[q]?).map (Work.ORDunwoody.Dunwoody.MidV.label (D := D)) = some e := by
  -- `chords l` is the `flatMap` over the fibres of `pairUp` applied to the positions of that
  -- fibre, so membership in it exposes the fibre `e` explicitly.
  rw [Work.ORDunwoody.Dunwoody.chords] at h
  rcases List.mem_flatMap.mp h with ⟨e, -, hpq⟩
  -- the two ends of a pair produced by `pairUp` are entries of the list it was applied to
  obtain ⟨hp_mem, hq_mem⟩ :=
    cwc_pairUp_mem (Work.ORDunwoody.Dunwoody.positionsOfLabel l e) p q hpq
  -- and membership in the positions of the fibre `e` is exactly "the visit is labelled `e`"
  exact ⟨e, hpq, ((cwc_mem_positionsOfLabel_iff (D := D)).mp hp_mem).2,
    ((cwc_mem_positionsOfLabel_iff (D := D)).mp hq_mem).2⟩

end Work.ORDunwoody.ChordWalk
