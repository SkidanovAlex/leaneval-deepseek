import Mathlib.GroupTheory.Index

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

theorem relIndex_mul_card_of_le {G : Type*} [Group G] {S T : Subgroup G} (h : S ≤ T) :
    S.relIndex T * Nat.card S = Nat.card T := by
  have key : (S.subgroupOf T).index * Nat.card (S.subgroupOf T) = Nat.card T :=
    (S.subgroupOf T).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at key
  exact key

end Commons.GroupTheory.Subgroup