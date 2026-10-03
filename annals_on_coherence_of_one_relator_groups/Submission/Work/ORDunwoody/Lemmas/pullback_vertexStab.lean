import Mathlib
import Submission.Work.ORDunwoody.Basic

namespace Work.ORDunwoody.Lemmas

open Work.ORDunwoody

theorem pullback_vertexStab {G H : Type*} [Group G] [Group H] {V : Type*} [MulAction G V]
    [MulAction H V] (π : H →* G) (h : ∀ (a : H) (v : V), a • v = π a • v)
    (T : GTree G V) (v : V) :
    (T.pullback π h).vertexStab v = (T.vertexStab v).comap π := by
  ext a
  simp only [GTree.vertexStab, Subgroup.mem_comap, MulAction.mem_stabilizer_iff, h a v]

end Work.ORDunwoody.Lemmas
