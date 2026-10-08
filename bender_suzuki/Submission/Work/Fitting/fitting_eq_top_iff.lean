import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.fitting_isNilpotent

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `F(G) = ⊤ ↔ G` is nilpotent

`F(G) = Work.Fitting.fitting G` is the supremum of the normal nilpotent subgroups of `G`
(`Submission.Work.Fitting.Defs`).  For a finite group we show

  `F(G) = ⊤ ↔ G is nilpotent`.

* If `F(G) = ⊤` then, since `F(G)` itself is nilpotent (`Work.Fitting.fitting_isNilpotent`),
  the group `G ≃ ↥F(G)` is nilpotent.
* Conversely if `G` is nilpotent then the whole group `⊤` is a normal nilpotent subgroup,
  so `⊤ ≤ F(G)`, whence `F(G) = ⊤`.
-/

namespace Work.Fitting

theorem fitting_eq_top_iff (G : Type*) [Group G] [Finite G] :
    Work.Fitting.fitting G = ⊤ ↔ Group.IsNilpotent G := by
  constructor
  · intro h
    have hnil : Group.IsNilpotent ↥(⊤ : Subgroup G) := h ▸ fitting_isNilpotent G
    exact Group.nilpotent_of_mulEquiv Subgroup.topEquiv
  · intro h
    refine le_antisymm le_top ?_
    exact le_fitting (N := ⊤) inferInstance (Group.nilpotent_of_mulEquiv Subgroup.topEquiv.symm)

end Work.Fitting
