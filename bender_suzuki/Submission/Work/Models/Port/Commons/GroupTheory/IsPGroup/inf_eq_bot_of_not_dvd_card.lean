import Mathlib.GroupTheory.PGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.IsPGroup

theorem inf_eq_bot_of_not_dvd_card {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact (Nat.Prime p)] {U T : Subgroup G} (hU : IsPGroup p U)
    (hT : ¬ p ∣ Nat.card T) : U ⊓ T = ⊥ := by
  have hp : IsPGroup p (U ⊓ T : Subgroup G) := hU.to_inf_left
  have hdvd : Nat.card (U ⊓ T : Subgroup G) ∣ Nat.card T :=
    Subgroup.card_dvd_of_le inf_le_right
  have hnp : ¬ p ∣ Nat.card (U ⊓ T : Subgroup G) := fun h => hT (h.trans hdvd)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hn0 : n = 0 := by
    by_contra h
    exact hnp (by rw [hn]; exact dvd_pow_self p h)
  rw [Subgroup.eq_bot_iff_card, hn, hn0, pow_zero]

end Commons.GroupTheory.IsPGroup