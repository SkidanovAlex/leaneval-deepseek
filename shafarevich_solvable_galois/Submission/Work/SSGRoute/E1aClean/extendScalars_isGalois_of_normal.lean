import Mathlib
import Submission.Work.SSGRoute.E1aClean.extendScalars_finDimensional_of_ker
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `F / U` is Galois when `Gal(K'/F) ⊆ Gal(K'/U)` is normal

Let `K'/κ` be a (possibly infinite) Galois extension and let `U ≤ F` be intermediate fields.
The assignment of subgroups of `Gal(K'/κ)` to intermediate fields is inclusion-reversing, so
`Gal(K'/F) ≤ Gal(K'/U)`, i.e. `Gal(K'/F)` is the subgroup `F.fixingSubgroup.subgroupOf
U.fixingSubgroup` of `U.fixingSubgroup = Gal(K'/κ)` restricted to `U`.

This file relates that subgroup to the Galois theory of the base-changed extension `F/U`: the
fixing subgroup of `F` viewed inside `Gal(K'/U)` is (the image under the change-of-base
isomorphism `IntermediateField.fixingSubgroupEquiv U` of) `Gal(K'/F)`. Consequently, if the latter
is normal in `Gal(K'/U)`, the fixed field `F/U` is Galois, by the infinite Galois correspondence
(`InfiniteGalois.normal_iff_isGalois`).

The subgroup identity is proved in `extendScalars_finDimensional_of_ker` as
`map_fixingSubgroupEquiv_subgroupOf`, and is reused here.
-/

namespace Work.SSGRoute.E1aClean

theorem extendScalars_isGalois_of_normal {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsGalois κ K'] {U F : IntermediateField κ K'} (h : U ≤ F)
    (hN : (F.fixingSubgroup.subgroupOf U.fixingSubgroup).Normal) :
    IsGalois ↥U ↥(IntermediateField.extendScalars h) := by
  -- The infinite Galois correspondence: `F/U` is Galois iff `Gal(K'/F)` is normal in `Gal(K'/U)`.
  rw [← InfiniteGalois.normal_iff_isGalois (IntermediateField.extendScalars h)]
  -- Identify `Gal(K'/F)` inside `Gal(K'/U)` with the image of `Gal(K'/F) ≤ Gal(K'/κ)`.
  rw [← map_fixingSubgroupEquiv_subgroupOf h]
  -- Normality is preserved and reflected by the change-of-base isomorphism.
  exact hN.map _ (IntermediateField.fixingSubgroupEquiv U).surjective

end Work.SSGRoute.E1aClean
