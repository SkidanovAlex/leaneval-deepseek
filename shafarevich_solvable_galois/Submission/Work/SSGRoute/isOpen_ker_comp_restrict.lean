import Mathlib.FieldTheory.KrullTopology
import Submission.Work.SSGRoute.isOpen_map_fixingSubgroupEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped IntermediateField Topology

namespace Work.SSGRoute

/-- The kernel of the pullback of a hom `χ : Gal(Ω/κ) →* M` with open kernel along the restriction
map `Gal(Ω/↥L) →* Gal(Ω/κ)` (a `↥L`-algebra automorphism is a `κ`-algebra automorphism) is again
open for the Krull topology. -/
theorem isOpen_ker_comp_restrict {κ Ω M : Type*} [Field κ] [Field Ω] [Algebra κ Ω] [Group M]
    (L : IntermediateField κ Ω) (χ : Gal(Ω/κ) →* M)
    (hχ : IsOpen (χ.ker : Set Gal(Ω/κ))) :
    IsOpen ((χ.comp ((Subgroup.subtype L.fixingSubgroup).comp
      (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom)).ker : Set Gal(Ω/↥L)) := by
  -- `e` identifies the fixing subgroup of `L` with `Gal(Ω/↥L)`, and the composite map in the
  -- statement is `χ` precomposed with the coercion `L.fixingSubgroup →* Gal(Ω/κ)` under `e`.
  set e : ↥L.fixingSubgroup ≃* Gal(Ω/↥L) := IntermediateField.fixingSubgroupEquiv L with he
  -- `H` is the subgroup of the fixing subgroup on which `χ` vanishes.
  set H : Subgroup ↥L.fixingSubgroup := χ.ker.comap (Subgroup.subtype L.fixingSubgroup) with hHdef
  have hH : IsOpen (H : Set ↥L.fixingSubgroup) := by
    have h : (H : Set ↥L.fixingSubgroup) = Subtype.val ⁻¹' (χ.ker : Set Gal(Ω/κ)) := by
      rw [hHdef]; rfl
    rw [h]
    exact hχ.preimage continuous_subtype_val
  -- The kernel of the composite is the preimage of `H` under the inverse of `e`.
  have hcomp : (χ.comp ((Subgroup.subtype L.fixingSubgroup).comp e.symm.toMonoidHom)).ker
      = H.comap e.symm.toMonoidHom := by
    rw [← MonoidHom.comap_ker, ← Subgroup.comap_comap]
  -- ... equivalently the image of `H` under `e`.
  have hkey : H.map e.toMonoidHom = H.comap e.symm.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_comap]
    constructor
    · rintro ⟨h, hh, rfl⟩
      change e.symm (e h) ∈ H
      rwa [MulEquiv.symm_apply_apply]
    · rintro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  rw [← hkey.trans hcomp.symm]
  exact isOpen_map_fixingSubgroupEquiv L H hH

end Work.SSGRoute
