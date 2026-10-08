import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Skeleton

/-- An injective homomorphism between finite groups maps the source into a subgroup of the
target (`Subgroup.card_dvd_of_injective`, Lagrange's theorem), so the order of the source
divides the order of the target; an odd number cannot have an even divisor. -/
theorem odd_card_of_injective {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (f : H →* G) (hf : Function.Injective f) (hodd : Odd (Nat.card G)) : Odd (Nat.card H) :=
  Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective f hf)

end Work.Skeleton
