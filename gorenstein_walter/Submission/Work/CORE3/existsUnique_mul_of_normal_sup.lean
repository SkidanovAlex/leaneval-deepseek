import Mathlib

namespace Work.CORE3

open scoped Pointwise

/-- If `H = U ⊔ S` with `U` normal in `H` and `U ⊓ S = ⊥`, then every `x ∈ H`
factors uniquely as a product `u * s` with `u ∈ U`, `s ∈ S`.

Existence comes from `H = U ⊔ S = U * S` (the set product), which holds because
`S` normalizes `U`; uniqueness from `U ⊓ S = ⊥`. -/
theorem existsUnique_mul_of_normal_sup {G : Type} [Group G] (U S H : Subgroup G)
    (hUH : U ≤ H) (hSH : S ≤ H) (hUnorm : (U.subgroupOf H).Normal)
    (hUS : U ⊔ S = H) (hdisj : U ⊓ S = ⊥) (x : G) (hx : x ∈ H) :
    ∃! p : ↥U × ↥S, (p.1 : G) * (p.2 : G) = x := by
  -- `S` lies in the normalizer of `U`, since `U` is normal in `H ⊇ S`.
  have hHnormU : H ≤ Subgroup.normalizer U :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mp hUnorm
  have hSnormU : S ≤ Subgroup.normalizer U := hSH.trans hHnormU
  -- hence `U ⊔ S = U * S` as sets, and `x ∈ H = U ⊔ S` factors.
  have hxsup : x ∈ U ⊔ S := by rw [hUS]; exact hx
  have hprod : x ∈ (U : Set G) * (S : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left U S hSnormU]
    exact hxsup
  obtain ⟨u, hu, s, hs, hus⟩ := Set.mem_mul.mp hprod
  refine ⟨(⟨u, hu⟩, ⟨s, hs⟩), hus, ?_⟩
  -- uniqueness
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ hq
  have h : a * b = u * s := hq.trans hus.symm
  have hU : u⁻¹ * a ∈ U := U.mul_mem (U.inv_mem hu) ha
  have hS : s * b⁻¹ ∈ S := S.mul_mem hs (S.inv_mem hb)
  -- `u⁻¹ * a = s * b⁻¹` lies in `U ⊓ S = ⊥`, hence is `1`.
  have heq : u⁻¹ * a = s * b⁻¹ := by
    calc u⁻¹ * a = u⁻¹ * (a * b) * b⁻¹ := by group
      _ = u⁻¹ * (u * s) * b⁻¹ := by rw [h]
      _ = s * b⁻¹ := by group
  have hmem : u⁻¹ * a ∈ U ⊓ S := ⟨hU, by rw [heq]; exact hS⟩
  have hone : u⁻¹ * a = 1 := by
    have hmem' : u⁻¹ * a ∈ (⊥ : Subgroup G) := by rw [← hdisj]; exact hmem
    exact Subgroup.mem_bot.mp hmem'
  have hsb : s * b⁻¹ = 1 := heq ▸ hone
  have ha_eq : (⟨a, ha⟩ : ↥U) = ⟨u, hu⟩ := Subtype.ext (inv_mul_eq_one.mp hone).symm
  have hb_eq : (⟨b, hb⟩ : ↥S) = ⟨s, hs⟩ := Subtype.ext (mul_inv_eq_one.mp hsb).symm
  exact Prod.ext ha_eq hb_eq

end Work.CORE3
