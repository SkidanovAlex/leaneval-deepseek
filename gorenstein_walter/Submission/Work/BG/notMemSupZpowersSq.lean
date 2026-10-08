import Mathlib

namespace Work.BG

/-- If `U` is a normal subgroup of a finite group `X` with `U ⊓ ⟨g⟩ = ⊥` and `g` has
even order, then `g` does not lie in `U ⊔ ⟨g ^ 2⟩`.

Proof: an element of `U ⊔ ⟨g²⟩` (with `U` normal) is `u * v` with `u ∈ U`, `v ∈ ⟨g²⟩ ≤ ⟨g⟩`.
Since `v ∈ ⟨g⟩`, also `u = g * v⁻¹ ∈ ⟨g⟩`, whence `u ∈ U ⊓ ⟨g⟩ = ⊥`, so `u = 1` and
`g = v ∈ ⟨g²⟩`.  Writing `g = (g²)^k` gives `g ^ (2k - 1) = 1`, so `orderOf g ∣ 2k - 1`;
but `2k - 1` is odd while `orderOf g` is even — contradiction. -/
theorem notMemSupZpowersSq {X : Type} [Group X] [Finite X]
    {U : Subgroup X} [U.Normal] {g : X} (hinf : U ⊓ Subgroup.zpowers g = ⊥)
    (heven : Even (orderOf g)) : g ∉ U ⊔ Subgroup.zpowers (g ^ 2) := by
  intro hg
  rw [Subgroup.mem_sup_of_normal_left] at hg
  obtain ⟨u, hu, v, hv, huv⟩ := hg
  -- `v ∈ ⟨g²⟩ ≤ ⟨g⟩`
  have hle : Subgroup.zpowers (g ^ 2) ≤ Subgroup.zpowers g :=
    Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) 2)
  have hvg : v ∈ Subgroup.zpowers g := hle hv
  -- `u = g * v⁻¹ ∈ ⟨g⟩`
  have hu_eq : u = g * v⁻¹ := by rw [← huv]; group
  have huzp : u ∈ Subgroup.zpowers g := by
    rw [hu_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers g) (Subgroup.inv_mem _ hvg)
  -- hence `u ∈ U ⊓ ⟨g⟩ = ⊥`, so `u = 1`
  have hu1 : u = 1 := by
    have h : u ∈ (⊥ : Subgroup X) := by
      rw [← hinf]
      exact Subgroup.mem_inf.mpr ⟨hu, huzp⟩
    exact Subgroup.mem_bot.mp h
  -- so `g = v ∈ ⟨g²⟩`
  have hgv : g = v := by rw [← huv, hu1, one_mul]
  have hgzp : g ∈ Subgroup.zpowers (g ^ 2) := hgv.symm ▸ hv
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgzp
  -- `g ^ (2k) = g`, hence `g ^ (2k - 1) = 1`
  have hA : (g ^ (2 : ℤ)) ^ k = g := by
    rw [← zpow_natCast g 2] at hk
    exact hk
  have h2k : g ^ ((2 : ℤ) * k) = g := by
    rw [zpow_mul]
    exact hA
  have h1 : g ^ ((2 : ℤ) * k - 1) = 1 := by
    rw [zpow_sub_one, h2k, mul_inv_cancel]
  -- so `orderOf g ∣ 2k - 1`
  have hdvd : (↑(orderOf g) : ℤ) ∣ ((2 : ℤ) * k - 1) :=
    orderOf_dvd_iff_zpow_eq_one.mpr h1
  -- but `orderOf g` is even while `2k - 1` is odd
  have h2dvd_orderOf : (2 : ℕ) ∣ orderOf g := even_iff_two_dvd.mp heven
  obtain ⟨m, hm⟩ := h2dvd_orderOf
  rw [hm] at hdvd
  push_cast at hdvd
  have h2dvd : (2 : ℤ) ∣ ((2 : ℤ) * k - 1) := dvd_trans ⟨(m : ℤ), rfl⟩ hdvd
  have hev : Even ((2 : ℤ) * k - 1) := even_iff_two_dvd.mpr h2dvd
  have hne : ¬ Even ((2 : ℤ) * k - 1) := by
    intro h
    obtain ⟨j, hj⟩ := h
    omega
  exact absurd hev hne

end Work.BG
