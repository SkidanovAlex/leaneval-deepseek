import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Skeleton

theorem card_subgroup_lt_card {G : Type*} [Group G] [Finite G] (H : Subgroup G) (hH : H ≠ ⊤) :
    Nat.card H < Nat.card G := by
  have h : (H : Set G) ≠ Set.univ := by
    intro h'
    exact hH (SetLike.coe_set_eq.mp h')
  have hlt := Set.ncard_lt_card h
  rwa [show Nat.card H = (H : Set G).ncard from Nat.card_coe_set_eq (H : Set G)]

end Work.Skeleton
