import Mathlib

open scoped Pointwise

namespace Work.CORE4.A4bAux

/-- If `Z` is a subgroup of the centre of `H`, then every element of `A ⊔ Z` can be written
as a product `c * z` with `c ∈ A` and `z ∈ Z`. -/
theorem exists_mul_of_mem_sup_of_le_center {H : Type*} [Group H] {Z A : Subgroup H}
    (hZc : Z ≤ Subgroup.center H) {x : H} (hx : x ∈ A ⊔ Z) :
    ∃ c ∈ A, ∃ z ∈ Z, c * z = x := by
  have hZn : Z.Normal := Subgroup.normal_of_le_center hZc
  have hx' : x ∈ (A : Set H) * (Z : Set H) := by
    rw [← Subgroup.mul_normal A Z (hN := hZn)]
    exact hx
  rwa [Set.mem_mul] at hx'

/-- If `x ^ (2 ^ k) = 1` for some `k` and `x ∈ A ⊔ Z` with `Z` central of odd order and
`A ⊓ Z = ⊥`, then `x ∈ A`. -/
theorem mem_of_mem_sup_of_pow_two_pow_eq_one {H : Type*} [Group H] {Z A : Subgroup H}
    (hZc : Z ≤ Subgroup.center H) (hinf : A ⊓ Z = ⊥) (hZodd : Odd (Nat.card ↥Z))
    {x : H} (hx : x ∈ A ⊔ Z) {k : ℕ} (hxk : x ^ (2 ^ k) = 1) : x ∈ A := by
  obtain ⟨c, hc, z, hz, hcz⟩ := exists_mul_of_mem_sup_of_le_center hZc hx
  -- `x ^ (2 ^ k) = 1` transfers to `c * z`
  have hczpow : (c * z) ^ (2 ^ k) = 1 := by rw [hcz]; exact hxk
  have hcomm : Commute c z := by
    have : z ∈ Subgroup.center H := hZc hz
    rw [Subgroup.mem_center_iff] at this
    exact this c
  have hcz' : c ^ (2 ^ k) * z ^ (2 ^ k) = 1 := by
    rw [← hcomm.mul_pow]; exact hczpow
  -- hence `z ^ (2 ^ k) = 1`, and `z` lies in `A` since it is the inverse of `c ^ (2^k)`
  have hzpow : z ^ (2 ^ k) = 1 := by
    have heq : z ^ (2 ^ k) = (c ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_right hcz'
    have hmem : z ^ (2 ^ k) ∈ A := by
      rw [heq]
      exact Subgroup.inv_mem A (Subgroup.pow_mem A hc (2 ^ k))
    have : z ^ (2 ^ k) ∈ A ⊓ Z := Subgroup.mem_inf.mpr ⟨hmem, Subgroup.pow_mem Z hz (2 ^ k)⟩
    rw [hinf] at this
    simpa using this
  -- `z` has odd order and is killed by the 2-power `2 ^ k`, so `z = 1`
  have hz1 : z = 1 := by
    have hdiv : orderOf z ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hzpow
    have hodd : Odd (orderOf z) := by
      have h2 : Odd (orderOf (⟨z, hz⟩ : Z)) :=
        Odd.of_dvd_nat hZodd (orderOf_dvd_natCard (⟨z, hz⟩ : Z))
      have h3 : orderOf (⟨z, hz⟩ : Z) = orderOf z :=
        (orderOf_injective (Subgroup.subtype Z) (Subgroup.subtype_injective Z)
          (⟨z, hz⟩ : Z)).symm
      exact h3 ▸ h2
    have hcop : Nat.Coprime (orderOf z) (2 ^ k) := (Nat.coprime_two_right.mpr hodd).pow_right k
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdiv)
  rw [← hcz, hz1, mul_one]
  exact hc

theorem normalizer_sup_of_central {H : Type*} [Group H] [Finite H] {Z A : Subgroup H}
    (hZc : Z ≤ Subgroup.center H) (hinf : A ⊓ Z = ⊥) (hA2 : IsPGroup 2 A)
    (hZodd : Odd (Nat.card ↥Z)) :
    Subgroup.normalizer ((A ⊔ Z : Subgroup H) : Set H) ≤ Subgroup.normalizer (A : Set H) := by
  -- a normalizer element sends every `a ∈ A` into `A`
  have key : ∀ u ∈ Subgroup.normalizer ((A ⊔ Z : Subgroup H) : Set H),
      ∀ a ∈ A, u * a * u⁻¹ ∈ A := by
    intro u hu a ha
    rw [Subgroup.mem_normalizer_iff] at hu
    have hx : u * a * u⁻¹ ∈ A ⊔ Z := (hu a).mp (Subgroup.mem_sup_left ha)
    obtain ⟨k, hk⟩ := hA2.exists_pow_pow_eq_one ⟨a, ha⟩
    have hk' : a ^ 2 ^ k = 1 := by
      have := congrArg (fun t : A => (t : H)) hk
      simpa [Subgroup.coe_pow] using this
    refine mem_of_mem_sup_of_pow_two_pow_eq_one hZc hinf hZodd hx (k := k) ?_
    rw [conj_pow, hk', mul_one, mul_inv_cancel]
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro a
  constructor
  · intro ha; exact key g hg a ha
  · intro ha
    have hg' : g⁻¹ ∈ Subgroup.normalizer ((A ⊔ Z : Subgroup H) : Set H) := inv_mem hg
    have h := key g⁻¹ hg' (g * a * g⁻¹) ha
    have hgg : g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a := by group
    rwa [hgg] at h

end Work.CORE4.A4bAux
