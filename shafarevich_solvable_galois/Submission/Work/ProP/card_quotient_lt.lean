import Mathlib.GroupTheory.Index
import Submission.Work.ProP.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

/-- The order of the quotient of a finite group by a nontrivial normal subgroup is strictly
smaller than the order of the group.

This is the standard "index times subgroup order" count: `Nat.card G = N.index * Nat.card N`
with `N.index > 0` and `Nat.card N > 1`. -/
theorem card_quotient_lt {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) : Nat.card (G ⧸ N) < Nat.card G := by
  have h1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hN
  have h2 : 0 < N.index := Nat.pos_of_ne_zero N.index_ne_zero_of_finite
  rw [← Subgroup.index_eq_card, ← Subgroup.index_mul_card]
  exact lt_mul_of_one_lt_right h2 h1

end Work.ProP
