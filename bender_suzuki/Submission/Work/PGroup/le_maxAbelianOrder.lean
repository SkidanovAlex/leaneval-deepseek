import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

theorem le_maxAbelianOrder {G : Type*} [Group G] (P A : Subgroup G) [Finite P] (hA : A ≤ P)
    (hab : IsMulCommutative A) : Nat.card A ≤ Work.PGroup.maxAbelianOrder P := by
  rw [maxAbelianOrder]
  refine le_csSup ?_ ⟨A, hA, hab, rfl⟩
  exact ⟨Nat.card P, fun n hn => by
    obtain ⟨B, hB, -, rfl⟩ := hn
    exact Subgroup.card_le_of_le hB⟩

end Work.PGroup
