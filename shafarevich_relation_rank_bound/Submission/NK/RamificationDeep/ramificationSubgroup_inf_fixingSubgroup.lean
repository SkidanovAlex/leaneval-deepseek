/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The higher ramification filtration and intermediate fields

For an intermediate field `M` of `L/K` and a valuation subring `A` of `L`, the `i`-th higher
ramification subgroup of `L/K` intersected with the fixing subgroup of `M` is the image of the
`i`-th higher ramification subgroup of `L/M`.  Concretely: the ramification filtration is
intrinsic to the `A`-valued "action on `A`", so passing to an intermediate base field does not
change it.

The file records the supporting lemmas (`fixingIncl`, `decompMap`, ...) and the main identity
`ramificationSubgroup_inf_fixingSubgroup`.
-/
import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.RamificationDeep.Defs

open scoped Pointwise

namespace NK.RamificationDeep

universe u

noncomputable section

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

/-- The canonical monoid homomorphism `Gal(L/M) → Gal(L/K)`: the fixing subgroup of `M` inside
`Gal(L/K)` is naturally identified with `Gal(L/M)`. -/
def fixingIncl (M : IntermediateField K L) : (L ≃ₐ[↥M] L) →* (L ≃ₐ[K] L) :=
  (M.fixingSubgroup).subtype.comp (IntermediateField.fixingSubgroupEquiv M).symm.toMonoidHom

@[simp]
theorem fixingIncl_apply (M : IntermediateField K L) (ψ : L ≃ₐ[↥M] L) (x : L) :
    (fixingIncl M ψ : L ≃ₐ[K] L) x = ψ x := rfl

/-- The two actions on the valuation ring `A` — that of `Gal(L/K)` and that of `Gal(L/M)`,
transported along `fixingIncl` — coincide. -/
theorem fixingIncl_smul (A : ValuationSubring L) (M : IntermediateField K L)
    (ψ : L ≃ₐ[↥M] L) : fixingIncl M ψ • A = ψ • A := by
  apply SetLike.ext
  intro x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor <;> rintro ⟨s, hs, hx⟩
  · exact ⟨s, hs, by rw [← hx]; rfl⟩
  · exact ⟨s, hs, by rw [← hx]; rfl⟩

/-- An element of `Gal(L/M)` stabilises `A` if and only if its image in `Gal(L/K)` does. -/
theorem mem_decompositionSubgroup_iff (A : ValuationSubring L) (M : IntermediateField K L)
    (ψ : L ≃ₐ[↥M] L) :
    ψ ∈ A.decompositionSubgroup ↥M ↔ fixingIncl M ψ ∈ A.decompositionSubgroup K := by
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff,
    ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff,
    fixingIncl_smul A M ψ]

/-- The map `Gal(L/M) ⊇ D_{L/M} → D_{L/K} ⊆ Gal(L/K)` induced by `fixingIncl`, restricted to the
decomposition subgroups. -/
def decompMap (A : ValuationSubring L) (M : IntermediateField K L) :
    (A.decompositionSubgroup ↥M) →* (A.decompositionSubgroup K) :=
  ((fixingIncl M).comp (A.decompositionSubgroup ↥M).subtype).codRestrict
    (A.decompositionSubgroup K)
    (fun σ => (mem_decompositionSubgroup_iff A M (σ : L ≃ₐ[↥M] L)).mp σ.2)

@[simp]
theorem decompMap_apply (A : ValuationSubring L) (M : IntermediateField K L)
    (σ : A.decompositionSubgroup ↥M) :
    ((decompMap A M σ : A.decompositionSubgroup K) : L ≃ₐ[K] L) =
      fixingIncl M (σ : L ≃ₐ[↥M] L) := rfl

/-- The restricted map `decompMap` is compatible with the actions on `A`. -/
theorem decompMap_smul (A : ValuationSubring L) (M : IntermediateField K L)
    (σ : A.decompositionSubgroup ↥M) (x : A) : decompMap A M σ • x = σ • x := by
  apply Subtype.ext
  rfl

/-- **The ramification condition is intrinsic**: an element of `Gal(L/M)` lies in the `i`-th
higher ramification subgroup of `L/M` if and only if its image in `Gal(L/K)` lies in the `i`-th
higher ramification subgroup of `L/K`. -/
theorem mem_ramificationSubgroup_iff (A : ValuationSubring L) (M : IntermediateField K L)
    (i : ℕ) (σ : A.decompositionSubgroup ↥M) :
    σ ∈ NK.Ramification.ramificationSubgroup (K := ↥M) A i ↔
      decompMap A M σ ∈ NK.Ramification.ramificationSubgroup (K := K) A i := by
  rw [NK.Ramification.mem_ramificationSubgroup_iff,
    NK.Ramification.mem_ramificationSubgroup_iff]
  simp only [decompMap_smul A M σ]

/-- The image of `decompMap` is exactly the set of decomposition elements of `L/K` that fix `M`
pointwise. -/
theorem range_decompMap (A : ValuationSubring L) (M : IntermediateField K L) :
    (decompMap A M).range
      = Subgroup.comap (A.decompositionSubgroup K).subtype (M.fixingSubgroup) := by
  ext σ
  rw [MonoidHom.mem_range, Subgroup.mem_comap]
  constructor
  · rintro ⟨τ, rfl⟩
    show ((decompMap A M τ : A.decompositionSubgroup K) : L ≃ₐ[K] L) ∈ M.fixingSubgroup
    rw [decompMap_apply]
    exact (IntermediateField.fixingSubgroupEquiv M).symm (τ : L ≃ₐ[↥M] L) |>.2
  · intro hσ
    let h : M.fixingSubgroup := ⟨(σ : L ≃ₐ[K] L), hσ⟩
    let ψ : L ≃ₐ[↥M] L := IntermediateField.fixingSubgroupEquiv M h
    have hψ : fixingIncl M ψ = (σ : L ≃ₐ[K] L) := rfl
    have hψmem : ψ ∈ A.decompositionSubgroup ↥M := by
      rw [mem_decompositionSubgroup_iff A M ψ, hψ]
      exact σ.2
    refine ⟨⟨ψ, hψmem⟩, ?_⟩
    apply Subtype.ext
    rw [decompMap_apply, hψ]

theorem ramificationSubgroup_inf_fixingSubgroup {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A] (M : IntermediateField K L)
    (i : ℕ) :
    ((NK.Ramification.ramificationSubgroup (K := K) A i).map
        (A.decompositionSubgroup K).subtype) ⊓ IntermediateField.fixingSubgroup M =
      (NK.Ramification.ramificationSubgroup (K := ↥M) A i).map
        ((M.fixingSubgroup).subtype.comp
          ((IntermediateField.fixingSubgroupEquiv M).symm.toMonoidHom.comp
            (A.decompositionSubgroup ↥M).subtype)) := by
  have hcomp : (M.fixingSubgroup).subtype.comp
        ((IntermediateField.fixingSubgroupEquiv M).symm.toMonoidHom.comp
          (A.decompositionSubgroup ↥M).subtype)
      = (A.decompositionSubgroup K).subtype.comp (decompMap A M) := by
    rw [← MonoidHom.comp_assoc]
    rfl
  have hmap : Subgroup.map (decompMap A M)
        (NK.Ramification.ramificationSubgroup (K := ↥M) A i)
      = NK.Ramification.ramificationSubgroup (K := K) A i ⊓ (decompMap A M).range := by
    have h1 : Subgroup.comap (decompMap A M)
          (NK.Ramification.ramificationSubgroup (K := K) A i)
        = NK.Ramification.ramificationSubgroup (K := ↥M) A i := by
      ext σ
      rw [Subgroup.mem_comap]
      exact mem_ramificationSubgroup_iff A M i σ
    rw [← h1, Subgroup.map_comap_eq, inf_comm]
  rw [hcomp, ← Subgroup.map_map, hmap,
    Subgroup.map_inf _ _ _ (Subgroup.subtype_injective _), range_decompMap,
    Subgroup.map_comap_eq, Subgroup.range_subtype]
  rw [← inf_assoc, inf_eq_left.mpr (Subgroup.map_subtype_le _)]

end

end NK.RamificationDeep
