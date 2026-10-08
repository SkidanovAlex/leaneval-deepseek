import Mathlib.Algebra.Torsor.Defs
import Mathlib.GroupTheory.PGroup
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.IsPGroup

/-- If `B = U ⊔ T` with `U ⊓ T = ⊥` and `T` normalizing `U`, then `[G : U] = [G : B] * |T|`.
Consequently, if `p` divides neither `[G : B]` nor `|T|`, it does not divide `[G : U]`. -/
theorem not_dvd_index_of_eq_sup {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact (Nat.Prime p)] (U T B : Subgroup G)
    (hB : B = U ⊔ T) (hUT : U ⊓ T = ⊥) (hTn : T ≤ Subgroup.normalizer (U : Set G))
    (hU : IsPGroup p U) (hT : ¬ p ∣ Nat.card T) (hBidx : ¬ p ∣ B.index) :
    ¬ p ∣ U.index := by
  have hUB : U ≤ B := by rw [hB]; exact le_sup_left
  -- `|B| = |U| * |T|` because `B = U ⊔ T` with trivial intersection and `T ≤ N(U)`.
  have hcardB : Nat.card ↥B = Nat.card ↥U * Nat.card ↥T := by
    rw [hB]
    exact Commons.GroupTheory.Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer U T hTn hUT
  -- `↥(U.subgroupOf B) ≃ ↥U`, so the two have the same cardinality.
  have hsub : Nat.card ↥(U.subgroupOf B) = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUB).toEquiv
  have hpos : 0 < Nat.card ↥U := Finite.card_pos
  -- `[B : U] = |T|`: both equal `|B| / |U|`.
  have hrelindex : (U.subgroupOf B).index = Nat.card ↥T := by
    have h1 : (U.subgroupOf B).index * Nat.card ↥(U.subgroupOf B) = Nat.card ↥B :=
      Subgroup.index_mul_card _
    rw [hsub, hcardB] at h1
    have h1' : Nat.card ↥U * (U.subgroupOf B).index = Nat.card ↥U * Nat.card ↥T := by
      rw [mul_comm (Nat.card ↥U) (U.subgroupOf B).index, h1]
    exact Nat.mul_left_cancel hpos h1'
  -- `[G : U] = [G : B] * [B : U]`.
  have hUidx : U.index = (U.subgroupOf B).index * B.index :=
    (Subgroup.relIndex_mul_index (H := U) (K := B) hUB).symm
  rw [hUidx, hrelindex]
  intro hp
  have hp' : p ∣ Nat.card ↥T ∨ p ∣ B.index := (Nat.Prime.dvd_mul (Fact.out)).mp hp
  exact hp'.elim hT hBidx

end Commons.GroupTheory.IsPGroup