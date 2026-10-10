import Mathlib
import Submission.Work.K3.BaseChange
import Submission.Work.K3.isReduced_tensor_rat

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3.isReduced_baseChange_rat` — base change of a reduced `ℚ`-scheme along a field extension

The base change of a reduced scheme `X` that is locally of finite type over `ℚ` along a field
extension `ℚ → L` is again reduced.  The mathematical content is that `ℚ` is perfect: a reduced
scheme locally of finite type over a perfect field is *geometrically reduced*, so its base
change to any field extension stays reduced.

The proof has two halves.

* **Field theory** (`Work.K3.isReduced_tensor_rat`, proved in the companion file): for fields
  `K, L` over `ℚ`, the ring `K ⊗[ℚ] L` is reduced.  (Equivalently: every field extension of
  `ℚ` is geometrically reduced.)
* **Geometry** (this file): the structure morphism `specMap ℚ L = Spec L ⟶ Spec ℚ` of a field
  extension is geometrically reduced.  For a field `K` and a morphism `Spec K ⟶ Spec ℚ`, the
  base change is `Spec (K ⊗[ℚ] L)` up to isomorphism (`pullbackSpecIso`), so `IsReduced` of the
  base change is exactly the field-theoretic statement above.  The conclusion for `X` then
  follows from `GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`, applied to the
  projection `baseChange ℚ L X ⟶ X` (the base change of the flat morphism `specMap ℚ L`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.K3

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

/-- **Base change of a field extension is geometrically reduced.**  The structure morphism
`Spec L ⟶ Spec ℚ` of a field extension `ℚ → L` is geometrically reduced: for every field `K`
and every morphism `Spec K ⟶ Spec ℚ` (with the induced `ℚ`-algebra structure on `K`), the
fibred product is `Spec (K ⊗[ℚ] L)`, which is reduced by `Work.K3.isReduced_tensor_rat`. -/
theorem geometricallyReduced_specMap_rat (L : Type) [Field L] [Algebra ℚ L] :
    GeometricallyReduced (specMap ℚ L) := by
  classical
  rw [GeometricallyReduced.eq_geometrically, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  -- The points of `Spec ℚ` are unique, so the `ℚ`-algebra structure on `K` induced by `y`
  -- is the canonical one.
  letI : Algebra ℚ K := (Spec.preimage y).hom.toAlgebra
  have hψ : (Spec.preimage y).hom = algebraMap ℚ K := (RingHom.algebraMap_toAlgebra _).symm
  have hy : Spec.preimage y = CommRingCat.ofHom (algebraMap ℚ K) :=
    CommRingCat.hom_ext (by rw [CommRingCat.hom_ofHom, hψ])
  rw [← Spec.map_preimage y, hy]
  -- The fibred product is `Spec (L ⊗[ℚ] K)`, and `L ⊗[ℚ] K = K ⊗[ℚ] L` is reduced.
  haveI : IsReduced (Spec (CommRingCat.of (L ⊗[ℚ] K))) :=
    (affine_isReduced_iff (CommRingCat.of (L ⊗[ℚ] K))).mpr (isReduced_tensor_rat L K)
  exact ObjectProperty.prop_of_iso IsReduced (pullbackSpecIso ℚ L K).symm ‹_›

/-- The base change `X ×_{Spec ℚ} Spec L` of a reduced `ℚ`-scheme of finite type along a field
extension is reduced. -/
theorem isReduced_baseChange_rat (L : Type) [Field L] [Algebra ℚ L]
    (X : AlgebraicGeometry.Scheme.{0}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of ℚ))]
    [AlgebraicGeometry.IsReduced X]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of ℚ))] :
    AlgebraicGeometry.IsReduced (Work.K3.baseChange ℚ L X) := by
  -- `X` is locally noetherian: it is locally of finite type over the locally noetherian
  -- scheme `Spec ℚ`.
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of ℚ)) := inferInstance
  haveI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of ℚ))
  -- The projection `baseChange ℚ L X ⟶ X` is flat with reduced (geometrically reduced) source.
  haveI : GeometricallyReduced (specMap ℚ L) := geometricallyReduced_specMap_rat L
  haveI : Flat (specMap ℚ L) := inferInstance
  show IsReduced (pullback (specMap ℚ L) (X ↘ Spec (CommRingCat.of ℚ)))
  infer_instance

end Work.K3
