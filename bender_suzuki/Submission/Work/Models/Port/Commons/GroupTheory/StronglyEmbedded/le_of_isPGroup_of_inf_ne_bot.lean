import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.isPGroup_inf_eq_bot_of_not_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

theorem le_of_isPGroup_of_inf_ne_bot {G : Type*} [Group G] [Finite G] (M : Subgroup G)
    (hOdd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    {T : Subgroup G} (hT : IsPGroup 2 T) (h : T ⊓ M ≠ ⊥) : T ≤ M := by
  by_contra hTM
  exact h (isPGroup_inf_eq_bot_of_not_le M hOdd hT hTM)

end Commons.GroupTheory.StronglyEmbedded
