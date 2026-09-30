/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The map `F ⊗[k] K(C) ⟶ K(C')` attached to a base-change square

For a curve `C` over a field `k`, a field extension `F/k` and a base-change square
`S : BCSquare C C'` (so that `C'` is a model of `C ×_k Spec F`), the projection `S.π` induces
a `k`-algebra map `S.fieldMap : K(C) ⟶ K(C')`.  Together with the structure map
`F ⟶ K(C')` this gives a `k`-algebra homomorphism

`tensorLift S : F ⊗[k] K(C) ⟶ K(C')`,  `c ⊗ x ↦ algebraMap F _ c * S.fieldMap.hom x`.

Its **injectivity** is the geometric content of the linear disjointness of `K(C)` and `F`
inside `K(C')`; it is the input to `linearIndependent_fieldMap`.

## Main declarations

* `functionFieldAlgebra`: restriction of scalars `k → F → K(C')` on the function field,
  i.e. `Algebra k K(C')` with `algebraMap k K(C') = algebraMap F K(C') ∘ algebraMap k F`.
* `tensorLift`, `tensorLift_tmul`, `tensorLift_one_tmul`, `tensorLift_smul`.

## Intended route to injectivity (used by `tensorLift_injective`)

Fix a nonempty affine open `W ⊆ C` and put `A = Γ(C, W)`, so that `K(C) = Frac A`
(`functionField_isFractionRing_of_isAffineOpen`).  Then

* the square obtained by pasting `isPullback_morphismRestrict S.π W` with `S.isPullback`
  exhibits `S.π ⁻¹ᵁ W` as the fibre product `W ×_{Spec k} Spec F`; comparing with
  `pullbackSpecIso` and `hW.isoSpec` gives `Γ(S.π ⁻¹ᵁ W) ≃+* (A ⊗[k] F)`
  (this is the analogue of `Curve.BaseChange.preimageIso` / `sectionsIso` in
  `Submission/Work/CurveBasics/BaseChange/krullDim_le_one.lean`, which do the tautological
  case `S = bcSquare C F`);
* `Scheme.germToFunctionField_injective` for the integral scheme `C'.left` shows
  `Γ(S.π ⁻¹ᵁ W) ⟶ K(C')` is injective;
* the composite `A ⊗[k] F → Γ(S.π ⁻¹ᵁ W) → K(C')` agrees with `tensorLift S` on pure tensors,
  because `fieldMap_germToFunctionField` identifies `S.fieldMap.hom ∘ germ_W` with
  `germ_{π ⁻¹ᵁ W} ∘ S.π.app W`, and `germToFunctionField` is compatible with the `F`-structure;
* finally `K(C) ⊗[k] F` is the localization of `A ⊗[k] F` at the image of the non-zero
  divisors of `A` (`IsLocalization.tensorProduct_tensorProduct`, as in
  `Work.CurveBasics.isDomain_tensor_of_fractionRing`), so injectivity descends from
  `A ⊗[k] F` to `K(C) ⊗[k] F`.
-/
import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMap_algebraMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Work.CurveBasics.Curve.BCSquare

variable {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
variable {C : Curve k} {C' : Curve F}

/-- Restriction of scalars along `k → F` for the function field of a curve over `F`: this is
the `k`-algebra structure with `algebraMap k K(C') = algebraMap F K(C') ∘ algebraMap k F`. -/
@[instance_reducible]
noncomputable def functionFieldAlgebra (C' : Curve F) : Algebra k C'.functionField :=
  Algebra.compHom C'.functionField (algebraMap k F)

attribute [local instance] functionFieldAlgebra

instance isScalarTowerFunctionField : IsScalarTower k F C'.functionField :=
  IsScalarTower.of_algebraMap_eq' rfl

@[simp] theorem functionFieldAlgebra_algebraMap (c : k) :
    algebraMap k C'.functionField c = algebraMap F C'.functionField (algebraMap k F c) := rfl

/-- The `k`-algebra homomorphism `F ⊗[k] K(C) ⟶ K(C')` attached to a base-change square:
on pure tensors it is `c ⊗ x ↦ algebraMap F _ c * S.fieldMap.hom x`. -/
noncomputable def tensorLift (S : BCSquare C C') : F ⊗[k] C.functionField →+* C'.functionField :=
  (Algebra.TensorProduct.lift
    (show F →ₐ[k] C'.functionField from
      { toRingHom := algebraMap F C'.functionField, commutes' := fun _ => rfl })
    (show C.functionField →ₐ[k] C'.functionField from
      { toRingHom := S.fieldMap.hom, commutes' := fun c => fieldMap_algebraMap S c })
    (fun _ _ => Commute.all _ _)).toRingHom

@[simp] theorem tensorLift_tmul (S : BCSquare C C') (c : F) (x : C.functionField) :
    tensorLift S (c ⊗ₜ[k] x) = algebraMap F C'.functionField c * S.fieldMap.hom x := by
  rw [tensorLift, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul]
  rfl

@[simp] theorem tensorLift_one_tmul (S : BCSquare C C') (x : C.functionField) :
    tensorLift S ((1 : F) ⊗ₜ[k] x) = S.fieldMap.hom x := by
  rw [tensorLift_tmul, map_one, one_mul]

/-- `tensorLift` is `F`-linear for the `F`-algebra structure of `F ⊗[k] K(C)`. -/
theorem tensorLift_smul (S : BCSquare C C') (c : F) (z : F ⊗[k] C.functionField) :
    tensorLift S (c • z) = c • tensorLift S z := by
  conv_lhs => rw [Algebra.smul_def]
  rw [map_mul, Algebra.smul_def]
  congr 1
  rw [show algebraMap F (F ⊗[k] C.functionField) c = c ⊗ₜ[k] (1 : C.functionField) from rfl]
  rw [tensorLift_tmul, map_one, mul_one]

end Work.CurveBasics.Curve.BCSquare
