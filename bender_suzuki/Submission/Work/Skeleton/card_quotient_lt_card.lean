import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Skeleton

theorem card_quotient_lt_card {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) : Nat.card (G ⧸ N) < Nat.card G := by
  -- Lagrange: |G| = |G ⧸ N| * |N|
  have hcard : Nat.card G = Nat.card (G ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  -- N is nontrivial, hence has at least 2 elements
  have hm : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hN
  -- the quotient is nonempty
  have hq : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  calc Nat.card (G ⧸ N) < Nat.card (G ⧸ N) * Nat.card N :=
        (Nat.lt_mul_iff_one_lt_right hq).mpr hm
    _ = Nat.card G := hcard.symm

end Work.Skeleton
