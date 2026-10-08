import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Skeleton

/-- A subgroup of a finite group of odd order has odd order: the order of a
subgroup divides the order of the group (Lagrange), and a divisor of an odd
number is odd. -/
theorem odd_card_subgroup {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G))
    (H : Subgroup G) : Odd (Nat.card H) := by
  obtain ⟨k, hk⟩ := Subgroup.card_subgroup_dvd_card H
  rw [hk] at hodd
  exact Nat.Odd.of_mul_left hodd

end Work.Skeleton
