import Mathlib
import Submission.Work.BSW.Defs

namespace Work.BSW.Cases

/-- The elements of `⟨w⟩` are `1` and `w` when `w` is an involution. -/
theorem mem_zpowers_of_orderOf_two {G : Type} [Group G] {w x : G}
    (hw : orderOf w = 2) (hx : x ∈ Subgroup.zpowers w) : x = 1 ∨ x = w := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : w ^ (2 : ℕ) = 1 := by
    have := pow_orderOf_eq_one w
    rw [hw] at this
    simpa using this
  have h1 : w ^ k = w ^ (k % (2 : ℤ)) := zpow_eq_zpow_emod' k h2
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left; rw [h1, hk, zpow_zero]
  · right; rw [h1, hk, zpow_one]

/-- In a group `G` with a subgroup `P` of order `5` whose normalizer `N_G(P)` has order `10` and
contains an involution `w` with `|P⟨w⟩| = 10`, the subgroup `D = ⟨w⟩` of order `2` is a complement
of `P` in `N_G(P)`: `N_G(P) = P ⋊ D`.  Every nontrivial subgroup of `D` is `D` itself, and any
involution `u ≠ w` commuting with `w` inverts `D`. -/
theorem bswK2Complement {G : Type} [Group G] [Finite G] (P : Subgroup G) {w : G}
    (hP : Nat.card ↥P = 5) (hN : Nat.card ↥(Subgroup.normalizer (P : Set G)) = 10)
    (hwN : w ∈ Subgroup.normalizer (P : Set G)) (hw : orderOf w = 2)
    (hu : ∃ u : G, orderOf u = 2 ∧ u ≠ w ∧ u * w = w * u)
    (hsup : Nat.card ↥(P ⊔ Subgroup.zpowers w) = 10) :
    ∃ D : Subgroup G, IsMulCommutative ↥D ∧ Nat.card ↥D = 2 ∧ P ⊓ D = ⊥ ∧
      Subgroup.normalizer (P : Set G) = P ⊔ D ∧
      (∀ X : Subgroup G, X ≠ ⊥ → X ≤ D →
        Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (D : Set G)) ∧
      (∃ u : G, orderOf u = 2 ∧ u ∉ D ∧ Work.GW2.Inverts u D) := by
  obtain ⟨u, hu_ord, hu_ne, hu_comm⟩ := hu
  -- `w` is an involution, so `w⁻¹ = w`.
  have hw2 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rw [hw] at this
    simpa [pow_two] using this
  have hwinv : w⁻¹ = w := by
    calc w⁻¹ = w⁻¹ * (w * w) := by rw [hw2, mul_one]
      _ = (w⁻¹ * w) * w := by rw [mul_assoc]
      _ = w := by rw [inv_mul_cancel, one_mul]
  have hD2 : Nat.card ↥(Subgroup.zpowers w) = 2 := by rw [Nat.card_zpowers, hw]
  -- The complement is `D = ⟨w⟩`.
  refine ⟨Subgroup.zpowers w, ?_, ?_, ?_, ?_, ?_, ⟨u, hu_ord, ?_, ?_⟩⟩
  · -- `D` is commutative (it is cyclic).
    infer_instance
  · -- `|D| = 2`.
    exact hD2
  · -- `P ⊓ D = ⊥`: its order divides both `5` and `2`.
    rw [← Subgroup.card_eq_one]
    have h5 : Nat.card ↥(P ⊓ Subgroup.zpowers w) ∣ 5 := by
      rw [← hP]; exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(P ⊓ Subgroup.zpowers w) ∣ 2 := by
      rw [← hD2]; exact Subgroup.card_dvd_of_le inf_le_right
    have := Nat.dvd_gcd h5 h2
    simpa using this
  · -- `N_G(P) = P ⊔ D`: both are contained in `N_G(P)` and have card `10`.
    have hle : P ⊔ Subgroup.zpowers w ≤ Subgroup.normalizer (P : Set G) :=
      sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hwN)
    have hcard : Nat.card ↥(Subgroup.normalizer (P : Set G)) =
        Nat.card ↥(P ⊔ Subgroup.zpowers w) := by rw [hN, hsup]
    exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm
  · -- Every nontrivial subgroup of `D` is `D` itself (as `|D| = 2`).
    intro X hXne hXle
    have hXD : X = Subgroup.zpowers w := by
      obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
      have hxX : (x : G) ∈ X := x.2
      have hxne' : (x : G) ≠ 1 := fun h => hxne (Subtype.ext h)
      have hxw : (x : G) = w := by
        rcases mem_zpowers_of_orderOf_two hw (hXle hxX) with h | h
        · exact absurd h hxne'
        · exact h
      have hle' : Subgroup.zpowers w ≤ X := Subgroup.zpowers_le.mpr (hxw ▸ hxX)
      exact le_antisymm hXle hle'
    rw [hXD]
  · -- `u ∉ D = ⟨w⟩`: the only non-identity element of `D` is `w`, but `u ≠ w`.
    intro hu_mem
    rcases mem_zpowers_of_orderOf_two hw hu_mem with h | h
    · rw [h, orderOf_one] at hu_ord; exact absurd hu_ord (by norm_num)
    · exact hu_ne h
  · -- `u` inverts `D`: it commutes with the generator `w`, an involution.
    intro x hx
    rcases mem_zpowers_of_orderOf_two hw hx with h | h
    · rw [h]; simp
    · rw [h, hwinv]
      calc u * w * u⁻¹ = (u * w) * u⁻¹ := by rw [mul_assoc]
        _ = (w * u) * u⁻¹ := by rw [hu_comm]
        _ = w * (u * u⁻¹) := by rw [mul_assoc]
        _ = w := by rw [mul_inv_cancel, mul_one]

end Work.BSW.Cases
