import Mathlib

namespace Work.CORE4NK

/-- A subgroup `Y` of odd order is trivial if some `s` inverts it and some `t` centralising it
satisfies `s ≡ t (mod Z(H))`: then `s * t⁻¹ ∈ Z(H)`, so `s` centralises `Y` as well, and every
`y ∈ Y` satisfies `y = y⁻¹` while `orderOf y` is odd. -/
theorem eq_bot_of_inverts_of_congruent_mod_center {H : Type*} [Group H] (Y : Subgroup H)
    (s t : H) (hYodd : Odd (Nat.card Y)) (hinv : ∀ y ∈ Y, s * y * s⁻¹ = y⁻¹)
    (hcent : ∀ y ∈ Y, t * y = y * t)
    (hcong : QuotientGroup.mk' (Subgroup.center H) s = QuotientGroup.mk' (Subgroup.center H) t) :
    Y = ⊥ := by
  -- `s` and `t` lie in the same coset of `Z(H)`, so `s * t⁻¹` is central.
  have h1 : QuotientGroup.mk' (Subgroup.center H) (s * t⁻¹) = 1 := by
    rw [map_mul, map_inv, hcong, mul_inv_cancel]
  have hmem : s * t⁻¹ ∈ Subgroup.center H := by
    rw [← QuotientGroup.eq_one_iff (s * t⁻¹), ← QuotientGroup.mk'_apply]
    exact h1
  have hc : ∀ g : H, g * (s * t⁻¹) = (s * t⁻¹) * g := Subgroup.mem_center_iff.mp hmem
  have hs_eq : s = (s * t⁻¹) * t := by group
  -- Hence `s` inverts `Y` exactly as the central element `s * t⁻¹` composed with `t` does:
  -- the central factor can be ignored, and the `t`-conjugation is trivial on `Y`.
  have hstep : ∀ y ∈ Y, s * y * s⁻¹ = y := by
    intro y hy
    have hty : t * y * t⁻¹ = y := by
      rw [hcent y hy, mul_assoc, mul_inv_cancel, mul_one]
    have hcy : (s * t⁻¹) * y * (s * t⁻¹)⁻¹ = y := by
      rw [← hc y, mul_assoc, mul_inv_cancel, mul_one]
    have hkey : s * y * s⁻¹ = (s * t⁻¹) * (t * y * t⁻¹) * (s * t⁻¹)⁻¹ := by
      conv_lhs => rw [hs_eq]
      group
    rw [hkey, hty, hcy]
  apply le_antisymm _ bot_le
  intro y hy
  rw [Subgroup.mem_bot]
  -- Combining `hstep` with `hinv`, every `y ∈ Y` satisfies `y = y⁻¹`.
  have hyinv : y = y⁻¹ := by
    have h := hinv y hy
    rw [hstep y hy] at h
    exact h
  have hy' : (⟨y, hy⟩ : Y) = (⟨y, hy⟩ : Y)⁻¹ := by
    ext
    simpa using hyinv
  have hsquare : (⟨y, hy⟩ : Y) * (⟨y, hy⟩ : Y) = 1 := (eq_inv_iff_mul_eq_one.mp hy')
  -- So `orderOf y ∣ 2`, while Lagrange gives `orderOf y ∣ Nat.card Y`, which is odd.
  have h2 : orderOf (⟨y, hy⟩ : Y) ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    rwa [pow_two]
  have hcard : orderOf (⟨y, hy⟩ : Y) ∣ Nat.card Y := orderOf_dvd_natCard _
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact Subtype.ext_iff.mp (orderOf_eq_one_iff.mp h)
  · exfalso
    rw [h] at hcard
    exact (Nat.not_even_iff_odd.mpr hYodd) (even_iff_two_dvd.mpr hcard)

end Work.CORE4NK
