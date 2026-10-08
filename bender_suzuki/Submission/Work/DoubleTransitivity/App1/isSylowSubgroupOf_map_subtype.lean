import Mathlib
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.DoubleTransitivity.App1

theorem isSylowSubgroupOf_map_subtype {G : Type} [Group G] [Finite G] {X : Subgroup G} {p : ℕ}
    (hp : p.Prime) (S : Sylow p ↥X) :
    Work.DoubleTransitivity.IsSylowSubgroupOf p ((S : Subgroup ↥X).map X.subtype) X := by
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨Subgroup.map_subtype_le (S : Subgroup ↥X), S.isPGroup'.map X.subtype, ?_⟩
  -- the image of `S` back down in `↥X` is `S` again, so the index is unchanged
  have hEq : ((S : Subgroup ↥X).map X.subtype).subgroupOf X = (S : Subgroup ↥X) := by
    rw [← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective (S : Subgroup ↥X)
  rw [hEq]
  exact Sylow.not_dvd_index S

end Work.DoubleTransitivity.App1
