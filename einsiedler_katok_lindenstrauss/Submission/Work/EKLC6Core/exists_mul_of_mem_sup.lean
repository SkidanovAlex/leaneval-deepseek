import Mathlib
import Submission.Work.EKLContract.Interfaces

namespace Work.EKLC6Core

/-- If `T` normalizes `U`, then the product set `T * U` is a subgroup of `G`, and
consequently every element of `T ⊔ U` factors as `g * u` with `g ∈ T` and `u ∈ U`. -/
theorem exists_mul_of_mem_sup {G : Type*} [Group G] {T U : Subgroup G}
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) {h : G} (hh : h ∈ T ⊔ U) :
    ∃ g ∈ T, ∃ u ∈ U, h = g * u := by
  -- The product set `T * U` is a subgroup when `T` normalizes `U`.
  let S : Subgroup G :=
    { carrier := {x | ∃ t ∈ T, ∃ u ∈ U, x = t * u}
      mul_mem' := by
        rintro x y ⟨t1, ht1, u1, hu1, rfl⟩ ⟨t2, ht2, u2, hu2, rfl⟩
        -- (t₁ u₁)(t₂ u₂) = (t₁ t₂) * ((t₂⁻¹ u₁ t₂) u₂)
        exact ⟨t1 * t2, T.mul_mem ht1 ht2, t2⁻¹ * u1 * t2 * u2,
          U.mul_mem (by simpa using hnorm t2⁻¹ (T.inv_mem ht2) u1 hu1) hu2, by group⟩
      one_mem' := ⟨1, T.one_mem, 1, U.one_mem, by group⟩
      inv_mem' := by
        rintro x ⟨t, ht, u, hu, rfl⟩
        -- (t u)⁻¹ = t⁻¹ * (t u⁻¹ t⁻¹)
        exact ⟨t⁻¹, T.inv_mem ht, t * u⁻¹ * t⁻¹,
          hnorm t ht u⁻¹ (U.inv_mem hu), by group⟩ }
  -- `S` contains both `T` and `U`, hence contains `T ⊔ U`.
  have hTU : T ⊔ U ≤ S :=
    sup_le (fun t ht => ⟨t, ht, 1, U.one_mem, by group⟩)
      (fun u hu => ⟨1, T.one_mem, u, hu, by group⟩)
  exact hTU hh

end Work.EKLC6Core
