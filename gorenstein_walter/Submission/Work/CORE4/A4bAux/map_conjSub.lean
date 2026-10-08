import Mathlib
import Submission.Work.CORE4.Defs

namespace Work.CORE4.A4bAux

theorem map_conjSub {G H : Type*} [Group G] [Group H] (f : G →* H) (e : G) (A : Subgroup G) :
    (Work.GW2.conjSub e A).map f = Work.GW2.conjSub (f e) (A.map f) := by
  rw [Work.GW2.conjSub, Work.GW2.conjSub, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply, map_mul]

end Work.CORE4.A4bAux
