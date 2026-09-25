import Mathlib
import Submission.NK.Reconstruct.LevelMap
import Submission.NK.Reconstruct.levelPairData

/-!
# The level correspondence of a homeomorphic isomorphism preserves composita

`NK.Reconstruct.levelMap ψ` is the correspondence of finite levels induced by an isomorphism
`ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)` of absolute Galois groups: it sends a level `L` to the fixed field of
the image of `Gal(Ω/L)` under `ψ`, i.e. it is the map on intermediate fields induced by `ψ` through
the Krull correspondence.  This file records its compatibility with the lattice operations:

* `NK.Reconstruct.fixedField_inf_of_isClosed` — the **compositum rule**: for *closed* subgroups
  `H₁, H₂ ≤ Gal(Ω/k)` the fixed field of `H₁ ⊓ H₂` is the compositum of the fixed fields.  This is
  the Krull correspondence read backwards: `(fixedField H₁ ⊔ fixedField H₂).fixingSubgroup` is
  `H₁ ⊓ H₂` (`IntermediateField.fixingSubgroup_sup`, `InfiniteGalois.fixingSubgroup_fixedField`),
  and `fixedField` is inverse to `fixingSubgroup`
  (`InfiniteGalois.fixedField_fixingSubgroup`).
  (Closedness is essential: `fixedField` only sees the topological closure of a subgroup.)
* `NK.Reconstruct.levelMap_sup` — **`levelMap ψ` preserves joins**:
  `levelMap ψ (L ⊔ M) = levelMap ψ L ⊔ levelMap ψ M` for finite levels `L, M`.

Indeed `levelMap ψ (L ⊔ M)` is the fixed field of
`(L ⊔ M).fixingSubgroup.map ψ = (L.fixingSubgroup ⊓ M.fixingSubgroup).map ψ
= L.fixingSubgroup.map ψ ⊓ M.fixingSubgroup.map ψ`
(`IntermediateField.fixingSubgroup_sup`, with `Subgroup.map` preserving `⊓` because `ψ` is
injective), and the two images are closed subgroups because the fixing subgroups are closed
(`InfiniteGalois.fixingSubgroup_isClosed`) and `ψ` is a homeomorphism (`IsHomeomorph` gives an open
map, and openness plus bijectivity gives closedness via `IsHomeomorph.homeomorph`).  The compositum
rule above then identifies the fixed field of the intersection with the compositum of the fixed
fields.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. XII;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.style.haveILetI false

namespace NK.Reconstruct

/-- **The compositum rule of the Krull correspondence**: for closed subgroups `H₁, H₂` of the
absolute Galois group `Gal(Ω/k)`, the fixed field of `H₁ ⊓ H₂` is the compositum of the fixed fields
of `H₁` and `H₂`.

Both directions are the Krull correspondence: `(fixedField H₁ ⊔ fixedField H₂).fixingSubgroup` is
`H₁ ⊓ H₂` because `fixingSubgroup` turns composites into intersections
(`IntermediateField.fixingSubgroup_sup`) and `fixedField` is inverse to `fixingSubgroup` on the
closed subgroups `H₁`, `H₂` (`InfiniteGalois.fixingSubgroup_fixedField`); and `fixedField` is
inverse to `fixingSubgroup` on the intermediate field `fixedField H₁ ⊔ fixedField H₂`
(`InfiniteGalois.fixedField_fixingSubgroup`). -/
theorem fixedField_inf_of_isClosed {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    {H₁ H₂ : Subgroup Gal(Ω/k)} (h₁ : IsClosed (H₁ : Set Gal(Ω/k)))
    (h₂ : IsClosed (H₂ : Set Gal(Ω/k))) :
    IntermediateField.fixedField (H₁ ⊓ H₂) =
      IntermediateField.fixedField H₁ ⊔ IntermediateField.fixedField H₂ := by
  have hfix : (IntermediateField.fixedField H₁ ⊔ IntermediateField.fixedField H₂).fixingSubgroup
      = H₁ ⊓ H₂ := by
    rw [IntermediateField.fixingSubgroup_sup,
      InfiniteGalois.fixingSubgroup_fixedField ⟨H₁, h₁⟩,
      InfiniteGalois.fixingSubgroup_fixedField ⟨H₂, h₂⟩]
  rw [← hfix, InfiniteGalois.fixedField_fixingSubgroup]

/-- **The level correspondence induced by a homeomorphic isomorphism of absolute Galois groups
preserves composita.** -/
theorem levelMap_sup {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K₁ K₂ : NK.Reconstruct.NumFieldIn ℚ Ω) [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω]
    (ψ : Gal(Ω/↥K₁.L) ≃* Gal(Ω/↥K₂.L)) (hψ : IsHomeomorph ψ)
    (L M : IntermediateField ↥K₁.L Ω) [FiniteDimensional ↥K₁.L L] [FiniteDimensional ↥K₁.L M] :
    NK.Reconstruct.levelMap ψ (L ⊔ M) = NK.Reconstruct.levelMap ψ L ⊔ NK.Reconstruct.levelMap ψ M := by
  haveI : IsGalois ↥K₁.L Ω := IsSepClosure.isGalois
  haveI : IsGalois ↥K₂.L Ω := IsSepClosure.isGalois
  -- The image of a fixing subgroup under the homeomorphism `ψ` is again closed.
  have hcl : ∀ X : IntermediateField ↥K₁.L Ω,
      IsClosed (((X.fixingSubgroup.map (ψ : Gal(Ω/↥K₁.L) →* Gal(Ω/↥K₂.L))) :
        Subgroup Gal(Ω/↥K₂.L)) : Set Gal(Ω/↥K₂.L)) := by
    intro X
    have h := hψ.homeomorph.isClosedMap (X.fixingSubgroup : Set Gal(Ω/↥K₁.L))
      (InfiniteGalois.fixingSubgroup_isClosed X)
    rw [Subgroup.coe_map]
    exact h
  rw [levelMap, levelMap, levelMap, IntermediateField.fixingSubgroup_sup]
  rw [Subgroup.map_inf _ _ _ ψ.injective]
  exact fixedField_inf_of_isClosed (hcl L) (hcl M)

end NK.Reconstruct
