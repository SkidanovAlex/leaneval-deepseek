import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Skeleton

theorem odd_index {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G)) (H : Subgroup G) :
    Odd H.index := by
  have h := hodd
  rw [← H.index_mul_card] at h
  exact (Nat.odd_mul.mp h).1

end Work.Skeleton
