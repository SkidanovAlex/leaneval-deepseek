import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- A `2`-subgroup and a subgroup of odd order intersect trivially: an element of the
intersection has order dividing a power of `2` (from the `2`-group) and dividing the odd
number `Nat.card B`, hence its order is `1`. -/
theorem isPGroup_two_inf_eq_bot_of_odd {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hA : IsPGroup 2 A) (hB : Odd (Nat.card ↥B)) : A ⊓ B = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgA, hgB⟩ := hg
  obtain ⟨k, hk⟩ := hA.exists_orderOf_dvd_pow ⟨g, hgA⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdB : orderOf g ∣ Nat.card ↥B := B.orderOf_dvd_natCard hgB
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥B) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; simp
    · rw [Nat.coprime_pow_left_iff hkpos]
      exact Nat.coprime_two_left.mpr hB
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hk hdB)

end Work.ZassenhausSuzuki
