import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Skeleton

/-- The quotient of a finite group of odd order by a normal subgroup has odd
order: `|G| = |G ⧸ N| * |N|` (Lagrange), and a factor of an odd number is odd. -/
theorem odd_card_quotient {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G))
    (N : Subgroup G) [N.Normal] : Odd (Nat.card (G ⧸ N)) := by
  have hcard : Nat.card G = Nat.card (G ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [hcard] at hodd
  exact (Nat.odd_mul.mp hodd).1

end Work.Skeleton
