import Mathlib
import Submission.Work.BSW.Cases.DataZass.Setup

namespace Work.BSW.Cases.DataZass

open Subgroup

/-! ## Two elementary helpers

`Dfree` needs only two small facts beyond the configuration `IsBSWConf`:

* the elements of `⟨u⟩` are `1` and `u` when `u` is an involution;
* `(q-1)/2 * 2 = q - 1` for odd `q` (so that `|N_G(D)| = |D| * |⟨u⟩| = q - 1`).
-/

/-- The elements of `⟨u⟩` are `1` and `u` when `u` is an involution. -/
private theorem mem_zpowers_eq_one_or_of_orderOf_two {G : Type*} [Group G] {u x : G}
    (hu : orderOf u = 2) (hx : x ∈ Subgroup.zpowers u) : x = 1 ∨ x = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : u ^ (2 : ℕ) = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    simpa using this
  have h1 : u ^ k = u ^ (k % (2 : ℤ)) := zpow_eq_zpow_emod' k h2
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left; rw [h1, hk, zpow_zero]
  · right; rw [h1, hk, zpow_one]

/-- `(q - 1) / 2 * 2 = q - 1` for odd `q`. -/
private theorem div_two_mul_two {q : ℕ} (hodd : Odd q) : (q - 1) / 2 * 2 = q - 1 := by
  obtain ⟨t, ht⟩ := hodd
  exact Nat.div_mul_cancel (⟨t, by omega⟩ : 2 ∣ q - 1)

/-- **`D` acts fixed-point-freely on `Q`**: no nonidentity element of `D` centralizes a
nonidentity element of `Q`.

Suppose `d ∈ D#` centralizes `c ∈ Q#`.  Then `c` commutes with `d`, hence normalizes `⟨d⟩`, and
since `⟨d⟩ ≠ ⊥` and `⟨d⟩ ≤ D` the configuration (Bender's (4), strengthened) gives
`N_G(⟨d⟩) = N_G(D)`; so `c ∈ Q ⊓ N_G(D)` is nontrivial.

But `N_G(D) = D ⊔ ⟨u⟩` with `u ∉ D` an involution inverting `D`.  Since `u` inverts `D` it
normalizes it, and `D ⊓ ⟨u⟩ = ⊥` (an element of `⟨u⟩` is `1` or `u`, and `u ∉ D`), so the
cardinality formula for `H ⊔ K` with `H ⊓ K = ⊥` gives `|N_G(D)| = |D| * 2 = q - 1`.

Now `Q ⊓ N_G(D)` is a subgroup of `Q`, so its order divides `q`, and of `N_G(D)`, so its order
divides `q - 1`; hence it is trivial, contradicting `c ≠ 1`.  (This is the "no `p`-element in
`N_G(D)`" statement, here phrased without reference to `p`.) -/
theorem Dfree {G : Type} [Group G] [Finite G] {q : ℕ} {Q D : Subgroup G} (hodd : Odd q)
    (h : IsBSWConf (G := G) q Q D) {d c : G} (hd : d ∈ D) (hd1 : d ≠ 1) (hc : c ∈ Q)
    (hc1 : c ≠ 1) : d * c * d⁻¹ ≠ c := by
  intro hcon
  -- `d` and `c` commute
  have hdc : d * c = c * d := by
    have h1 : (d * c * d⁻¹) * d = c * d := by rw [hcon]
    rw [show (d * c * d⁻¹) * d = d * c by group] at h1
    exact h1
  have hcd : c * d * c⁻¹ = d := by
    rw [← hdc]
    group
  -- `c` normalizes `⟨d⟩`
  have hconj_d : MulAut.conj c d = d := by
    rw [MulAut.conj_apply]
    exact hcd
  have hconj_d_inv : MulAut.conj c⁻¹ d = d := by
    rw [MulAut.conj_apply, inv_inv]
    calc c⁻¹ * d * c = c⁻¹ * (d * c) := by group
      _ = c⁻¹ * (c * d) := by rw [← hdc]
      _ = d := by group
  have hpow1 : ∀ i : ℤ, c * d ^ i * c⁻¹ = d ^ i := by
    intro i
    have hh : MulAut.conj c (d ^ i) = d ^ i := by rw [map_zpow, hconj_d]
    rwa [MulAut.conj_apply] at hh
  have hpow2 : ∀ i : ℤ, c⁻¹ * d ^ i * c = d ^ i := by
    intro i
    have hh : MulAut.conj c⁻¹ (d ^ i) = d ^ i := by rw [map_zpow, hconj_d_inv]
    rwa [MulAut.conj_apply, inv_inv] at hh
  have hcN_d : c ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, (hpow1 i).symm⟩
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      calc d ^ i = c⁻¹ * d ^ i * c := (hpow2 i).symm
        _ = c⁻¹ * (c * y * c⁻¹) * c := by rw [← hi]
        _ = y := by group
  -- hence `c` normalizes `D`
  have hcN : c ∈ Subgroup.normalizer (D : Set G) := by
    have hzd_ne : Subgroup.zpowers d ≠ ⊥ := by
      intro hbot
      exact hd1 (Subgroup.zpowers_eq_bot.mp hbot)
    have hzd_le : Subgroup.zpowers d ≤ D := Subgroup.zpowers_le.mpr hd
    have heq := h.normalizer_eq (X := Subgroup.zpowers d) hzd_ne hzd_le
    rwa [heq] at hcN_d
  -- `N_G(D) = D ⊔ ⟨u⟩` has order `q - 1`
  obtain ⟨u, hu2, huD, huInv, huNorm⟩ := h.exists_inverting_strong
  have hzp_le : Subgroup.zpowers u ≤ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx k hk
    rcases mem_zpowers_eq_one_or_of_orderOf_two hu2 hx with rfl | rfl
    · simpa using hk
    · rw [huInv k hk]
      exact D.inv_mem hk
  have hinf_zu : D ⊓ Subgroup.zpowers u = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxD, hxu⟩
    rcases mem_zpowers_eq_one_or_of_orderOf_two hu2 hxu with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hxD) huD
  have hcardND : Nat.card ↥(Subgroup.normalizer (D : Set G)) = q - 1 := by
    rw [huNorm, card_sup_of_inf_bot_of_le_normalizer hinf_zu hzp_le, h.card_D,
      Nat.card_zpowers, hu2, div_two_mul_two hodd]
  -- `Q ⊓ N_G(D) = ⊥`
  have hQinf : Q ⊓ Subgroup.normalizer (D : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxQ, hxN⟩
    have h1 : orderOf x ∣ q := by
      have h' := Subgroup.card_dvd_of_le (H := Subgroup.zpowers x) (K := Q)
        (Subgroup.zpowers_le.mpr hxQ)
      rwa [Nat.card_zpowers, h.card_Q] at h'
    have h2 : orderOf x ∣ q - 1 := by
      have h' := Subgroup.card_dvd_of_le (H := Subgroup.zpowers x)
        (K := Subgroup.normalizer (D : Set G)) (Subgroup.zpowers_le.mpr hxN)
      rwa [Nat.card_zpowers, hcardND] at h'
    have hq1 : 1 ≤ q := by
      obtain ⟨t, ht⟩ := hodd
      omega
    have h3 : orderOf x ∣ 1 := by
      have h' := Nat.dvd_sub h1 h2
      rwa [Nat.sub_sub_self hq1] at h'
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  exact hc1 (Subgroup.mem_bot.mp
    (hQinf ▸ (show c ∈ Q ⊓ Subgroup.normalizer (D : Set G) from ⟨hc, hcN⟩)))

end Work.BSW.Cases.DataZass
