import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Track
import Submission.Work.ORDunwoody.Dunwoody.Chord
import Submission.Work.ORDunwoody.Dunwoody.Pattern

namespace Work.ORDunwoody

universe u

theorem trackOf_eq_of_chord {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}
    (r : {r : FreeGroup (Fin P.n) // r ∈ P.rel}) (c : G) {p q : ℕ}
    (h : (p, q) ∈ Work.ORDunwoody.Dunwoody.chords
      (Work.ORDunwoody.Dunwoody.faceVisits D c (FreeGroup.toWord r.1)))
    {m m' : Work.ORDunwoody.Dunwoody.MidV D}
    (hm : (Work.ORDunwoody.Dunwoody.faceVisits D c (FreeGroup.toWord r.1))[p]? = some m)
    (hm' : (Work.ORDunwoody.Dunwoody.faceVisits D c (FreeGroup.toWord r.1))[q]? = some m') :
    Work.ORDunwoody.Dunwoody.trackOf m = Work.ORDunwoody.Dunwoody.trackOf m' := by
  by_cases hmm : m = m'
  · subst hmm; rfl
  · exact Work.ORDunwoody.Dunwoody.trackOf_eq_of_adj
      ⟨⟨r, c, p, q, Or.inl h, hm, hm'⟩, hmm⟩

end Work.ORDunwoody
