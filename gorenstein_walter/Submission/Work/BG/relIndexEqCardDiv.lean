import Mathlib

namespace Work.BG

theorem relIndexEqCardDiv {G : Type*} [Group G] [Finite G] (C H : Subgroup G) :
    C.relIndex H = Nat.card H / Nat.card ↥(C ⊓ H) := by
  have h := Subgroup.relIndex_mul_card C H
  rw [← h]
  exact (Nat.mul_div_left (C.relIndex H) (Nat.card_pos (α := ↥(C ⊓ H)))).symm

end Work.BG
