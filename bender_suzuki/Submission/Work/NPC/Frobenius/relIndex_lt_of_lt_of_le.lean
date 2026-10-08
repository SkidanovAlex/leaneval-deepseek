import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC.Frobenius

theorem relIndex_lt_of_lt_of_le {G : Type*} [Group G] [Finite G] {A B P : Subgroup G}
    (hA : A ≤ P) (hBP : B ≤ P) (hAB : A < B) :
    B.relIndex P < A.relIndex P := by
  have hAidx : A.relIndex P * P.index = A.index := Subgroup.relIndex_mul_index hA
  have hBidx : B.relIndex P * P.index = B.index := Subgroup.relIndex_mul_index hBP
  have hlt : B.index < A.index := Subgroup.index_strictAnti hAB
  have hp : 0 < P.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := P))
  rw [← hAidx, ← hBidx] at hlt
  exact (Nat.mul_lt_mul_right hp).mp hlt

end Work.NPC.Frobenius
