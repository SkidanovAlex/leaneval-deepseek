import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC.Frobenius

theorem relIndex_eq_of_card_eq {G : Type*} [Group G] [Finite G] {H K L : Subgroup G}
    (hH : H ≤ L) (hK : K ≤ L) (hcard : Nat.card ↥H = Nat.card ↥K) :
    H.relIndex L = K.relIndex L := by
  have h1 : Nat.card ↥(H.subgroupOf L) * H.relIndex L = Nat.card ↥L :=
    Subgroup.card_mul_index (H.subgroupOf L)
  have h2 : Nat.card ↥(K.subgroupOf L) * K.relIndex L = Nat.card ↥L :=
    Subgroup.card_mul_index (K.subgroupOf L)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv, hcard] at h1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv] at h2
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos) (h1.trans h2.symm)

end Work.NPC.Frobenius
