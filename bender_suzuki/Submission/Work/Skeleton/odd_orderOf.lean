import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Skeleton

/-- In a finite group of odd order, every element has odd order: the order of `x`
divides the order of the group, and a divisor of an odd number is odd. -/
theorem odd_orderOf {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G)) (x : G) :
    Odd (orderOf x) :=
  hodd.of_dvd_nat (orderOf_dvd_natCard x)

end Work.Skeleton
