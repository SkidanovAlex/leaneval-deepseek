import Mathlib

namespace Commons.GroupTheory.Subgroup

theorem card_sup_mul_card_inf_of_normal {G : Type*} [Group G] [Finite G] (H K : Subgroup G)
    (hK : K.Normal) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  -- General cardinality identity for a subgroup inclusion `S ≤ T`:
  -- `[T : S] * |S| = |T|`.
  have hrelcard : ∀ {S T : Subgroup G}, S ≤ T → S.relIndex T * Nat.card ↥S = Nat.card ↥T := by
    intro S T h
    have key : (S.subgroupOf T).index * Nat.card ↥(S.subgroupOf T) = Nat.card ↥T :=
      (S.subgroupOf T).index_mul_card
    rw [show Nat.card ↥(S.subgroupOf T) = Nat.card ↥S from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at key
    exact key
  -- The relative index of `K` in `H ⊔ K` equals the relative index of `H ⊓ K` in `H`.
  have hrel : K.relIndex (H ⊔ K) = (H ⊓ K).relIndex H := by
    rw [@Subgroup.relIndex_sup_right G _ H K hK, Subgroup.inf_relIndex_left]
  have e1 : K.relIndex (H ⊔ K) * Nat.card ↥K = Nat.card ↥(H ⊔ K) := hrelcard le_sup_right
  have e2 : (H ⊓ K).relIndex H * Nat.card ↥(H ⊓ K) = Nat.card ↥H := hrelcard inf_le_left
  calc
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K)
        = K.relIndex (H ⊔ K) * Nat.card ↥K * Nat.card ↥(H ⊓ K) := by rw [← e1]
    _ = Nat.card ↥K * ((H ⊓ K).relIndex H * Nat.card ↥(H ⊓ K)) := by
          rw [hrel]; ring
    _ = Nat.card ↥K * Nat.card ↥H := by rw [e2]
    _ = Nat.card ↥H * Nat.card ↥K := by ring

end Commons.GroupTheory.Subgroup
