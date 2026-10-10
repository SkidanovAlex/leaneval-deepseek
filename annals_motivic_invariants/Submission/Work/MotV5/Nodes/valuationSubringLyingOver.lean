import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Extending a valuation to an arbitrary field extension (Chevalley's theorem)

Every valuation ring of a field `F` extends to a valuation ring of any field extension `L`:
given `v : Valuation F Γ₀` there is `B : ValuationSubring L` with
`algebraMap F L x ∈ B ↔ x ∈ v.valuationSubring` for all `x : F`.

The proof uses Mathlib's Stacks 00IA (`LocalSubring.exists_le_valuationSubring` packaged as
`Ideal.image_subset_nonunits_valuationSubring`): the image `A` of `v.valuationSubring` in `L`
is a local subring of `L`, and any proper ideal of a local subring of a field is contained in
the nonunits of some valuation subring `B ⊇ A`.  If `algebraMap x ∈ B` but `x ∉ v.valuationSubring`,
then `x ≠ 0` and `x⁻¹ ∈ v.valuationSubring` is a nonunit, hence `algebraMap x⁻¹ ∈ B.nonunits`;
together with `algebraMap x ∈ B` this forces `1 ∈ B.nonunits`, a contradiction.
-/

namespace Work.MotV5.Nodes

open IsLocalRing

theorem valuationSubringLyingOver {F L Γ₀ : Type*} [Field F] [Field L] [Algebra F L]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) :
    ∃ B : ValuationSubring L, ∀ x : F, algebraMap F L x ∈ B ↔ x ∈ v.valuationSubring := by
  let A : Subring L := Subring.map (algebraMap F L) v.valuationSubring.toSubring
  let e : v.valuationSubring ≃+* A :=
    Subring.equivMapOfInjective v.valuationSubring.toSubring (algebraMap F L)
      (algebraMap F L).injective
  have he_apply : ∀ y : v.valuationSubring, A.subtype (e y) = algebraMap F L y := by
    intro y
    rw [show A.subtype (e y) = ((e y : A) : L) from rfl]
    exact @Subring.coe_equivMapOfInjective_apply F L _ _ v.valuationSubring.toSubring
      (algebraMap F L) (algebraMap F L).injective y
  have hIne : (maximalIdeal v.valuationSubring).map (e : v.valuationSubring →+* A) ≠ ⊤ := by
    intro h
    rw [Ideal.map_eq_top_of_bijective (e : v.valuationSubring →+* A) e.bijective] at h
    exact (maximalIdeal.isMaximal v.valuationSubring).ne_top h
  obtain ⟨B, hAB, hInu⟩ := Ideal.image_subset_nonunits_valuationSubring
    (A := A) ((maximalIdeal v.valuationSubring).map (e : v.valuationSubring →+* A)) hIne
  refine ⟨B, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · by_contra hxnot
    have hxinv : x⁻¹ ∈ v.valuationSubring := (ValuationSubring.mem_or_inv_mem _ x).resolve_left hxnot
    have hmem : (⟨x⁻¹, hxinv⟩ : v.valuationSubring) ∈ maximalIdeal v.valuationSubring :=
      ValuationSubring.coe_mem_nonunits_iff.mp
        ((ValuationSubring.inv_mem_nonunits_iff _).mpr (Or.inr hxnot))
    have he : e ⟨x⁻¹, hxinv⟩ ∈ (maximalIdeal v.valuationSubring).map
        (e : v.valuationSubring →+* A) :=
      Ideal.mem_map_of_mem _ hmem
    have hnuB : algebraMap F L x⁻¹ ∈ B.nonunits := by
      have h := hInu ⟨e ⟨x⁻¹, hxinv⟩, he, rfl⟩
      rwa [he_apply] at h
    have hminv : (⟨algebraMap F L x⁻¹, B.nonunits_le hnuB⟩ : B) ∈ maximalIdeal B :=
      ValuationSubring.coe_mem_nonunits_iff.mp hnuB
    have hprod : (⟨algebraMap F L x, hx⟩ * ⟨algebraMap F L x⁻¹, B.nonunits_le hnuB⟩ : B) ∈
        maximalIdeal B :=
      Ideal.mul_mem_left _ _ hminv
    have hx0 : x ≠ 0 := fun h0 => hxnot (h0 ▸ v.valuationSubring.zero_mem)
    have hone : (⟨algebraMap F L x, hx⟩ * ⟨algebraMap F L x⁻¹, B.nonunits_le hnuB⟩ : B) = 1 := by
      refine Subtype.ext ?_
      push_cast
      rw [← map_inv₀, ← map_mul, mul_inv_cancel₀ hx0, map_one]
    rw [hone] at hprod
    exact (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).mpr hprod)
  · exact hAB (Subring.mem_map.mpr ⟨x, hx, rfl⟩)

end Work.MotV5.Nodes
