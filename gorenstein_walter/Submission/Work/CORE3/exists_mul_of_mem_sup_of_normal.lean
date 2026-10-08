import Mathlib

namespace Work.CORE3

open scoped Pointwise

/-- If `V, U ≤ S` and `S` normalizes both `V` and `U` (elementwise conjugation),
then every element of `V ⊔ U` is a product `v * u` with `v ∈ V`, `u ∈ U`.

Indeed, `S` normalizing `V` implies `U ≤ Subgroup.normalizer V`, so the pointwise
product of the sets `V` and `U` is exactly the subgroup `V ⊔ U`. -/
theorem exists_mul_of_mem_sup_of_normal {G : Type*} [Group G] {S V U : Subgroup G}
    (hV : V ≤ S) (hU : U ≤ S)
    (hVn : ∀ s ∈ S, ∀ v ∈ V, s * v * s⁻¹ ∈ V)
    (hUn : ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) :
    ∀ x ∈ V ⊔ U, ∃ v ∈ V, ∃ u ∈ U, x = v * u := by
  -- `S` lies in the normalizer of `V`.
  have hSnormV : S ≤ Subgroup.normalizer (↑V : Set G) :=
    Subgroup.le_normalizer_iff.mpr hVn
  -- hence so does `U`, since `U ≤ S`.
  have hUnormV : U ≤ Subgroup.normalizer (↑V : Set G) := hU.trans hSnormV
  intro x hx
  -- the set product `V * U` equals the subgroup `V ⊔ U`.
  have hx' : x ∈ (V : Set G) * (U : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left V U hUnormV]
    exact hx
  obtain ⟨v, hv, u, hu, hvu⟩ := Set.mem_mul.mp hx'
  exact ⟨v, hv, u, hu, hvu.symm⟩

end Work.CORE3
