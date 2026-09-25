import Mathlib.RingTheory.Valuation.LocalSubring

set_option linter.style.haveILetI false

namespace Commons.RingTheory.Valuation

open IsLocalRing

theorem exists_valuationSubring_comap_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring K) : ∃ B : ValuationSubring L, B.comap (algebraMap K L) = A := by
  let f : A →+* L := (algebraMap K L).comp (Subring.subtype A.toSubring)
  obtain ⟨B, hB, hloc⟩ := IsLocalRing.exists_factor_valuationRing (f := f)
  haveI : IsLocalHom (f.codRestrict B.toSubring hB) := hloc
  refine ⟨B, le_antisymm ?_ ?_⟩
  · -- `B.comap (algebraMap K L) ≤ A`
    intro x hx
    rw [ValuationSubring.mem_comap] at hx
    by_contra hxA
    have hx0 : x ≠ 0 := fun h => hxA (h ▸ A.zero_mem)
    have hxinv : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hxA
    have hnu : ¬ IsUnit (⟨x⁻¹, hxinv⟩ : A) := by
      have hmem : (⟨x⁻¹, hxinv⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
        rw [← ValuationSubring.coe_mem_nonunits_iff]
        exact (ValuationSubring.inv_mem_nonunits_iff A).mpr (Or.inr hxA)
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
    have hunit : IsUnit ((f.codRestrict B.toSubring hB) ⟨x⁻¹, hxinv⟩) := by
      rw [isUnit_iff_exists_inv]
      refine ⟨⟨algebraMap K L x, hx⟩, ?_⟩
      apply Subtype.ext
      rw [Subring.coe_mul, Subring.coe_one, RingHom.codRestrict_apply]
      change (algebraMap K L) x⁻¹ * (algebraMap K L) x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    exact (fun h => hnu (IsLocalHom.map_nonunit _ h)) hunit
  · -- `A ≤ B.comap (algebraMap K L)`
    intro x hx
    rw [ValuationSubring.mem_comap]
    exact hB ⟨x, hx⟩

end Commons.RingTheory.Valuation