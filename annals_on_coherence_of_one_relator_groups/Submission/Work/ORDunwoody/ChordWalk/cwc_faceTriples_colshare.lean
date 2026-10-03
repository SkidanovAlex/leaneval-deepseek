import Mathlib
import Submission.Work.ORDunwoody.ChordWalk.StepDefs

universe u

namespace Work.ORDunwoody.ChordWalk

theorem cwc_faceTriples_colshare {G : Type u} [Group G] {V : Type u}
    [MulAction G V] {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (c : G) (w : List (Fin P.n × Bool))
    {k : ℕ} {a : Work.ORDunwoody.Dunwoody.BaseV D} {m : Work.ORDunwoody.Dunwoody.MidV D}
    {b : Work.ORDunwoody.Dunwoody.BaseV D}
    (h : (Work.ORDunwoody.Dunwoody.faceTriples D c w)[k]? = some (a, m, b))
    {a' : Work.ORDunwoody.Dunwoody.BaseV D} {m' : Work.ORDunwoody.Dunwoody.MidV D}
    {b' : Work.ORDunwoody.Dunwoody.BaseV D}
    (h' : (Work.ORDunwoody.Dunwoody.faceTriples D c w)[k + 1]? = some (a', m', b')) :
    Work.ORDunwoody.Dunwoody.colour D b = Work.ORDunwoody.Dunwoody.colour D a' := by
  -- `b`, the old vertex right after the `k`-th visit, lies in the arc of index `k + 1`;
  -- `a'`, the old vertex right before the `(k + 1)`-st visit, lies in the same arc.
  have hb : (b, k + 1) ∈
      Work.ORDunwoody.Dunwoody.arcIndex (Work.ORDunwoody.Dunwoody.faceWalk D c w) :=
    (Work.ORDunwoody.faceTriples_arcIndex (D := D) c w h).2.1
  have ha' : (a', k + 1) ∈
      Work.ORDunwoody.Dunwoody.arcIndex (Work.ORDunwoody.Dunwoody.faceWalk D c w) :=
    (Work.ORDunwoody.faceTriples_arcIndex (D := D) c w h').1
  exact Work.ORDunwoody.colour_arcIndex (D := D) c w hb ha'

end Work.ORDunwoody.ChordWalk
