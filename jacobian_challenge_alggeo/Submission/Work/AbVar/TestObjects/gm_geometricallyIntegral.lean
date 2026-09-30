import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.TestObjects

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

namespace Work.AbVar.TestObjects

open CategoryTheory Limits TensorProduct
open scoped TensorProduct
open AlgebraicGeometry

/-- For a field extension `K/k`, the base change `LaurentPolynomial k ⊗[k] K` is a domain,
being isomorphic to the Laurent polynomial ring `K[T;T⁻¹]` over `K`. -/
theorem isDomain_tensor_laurent (k K : Type*) [Field k] [Field K] [Algebra k K] :
    IsDomain (LaurentPolynomial k ⊗[k] K) := by
  have e1 : LaurentPolynomial k ⊗[k] K ≃ₐ[k] AddMonoidAlgebra (k ⊗[k] K) ℤ :=
    AddMonoidAlgebra.lTensorAlgEquiv k k K
  have e2 : k ⊗[k] K ≃ₐ[k] K := Algebra.TensorProduct.lid k K
  have e3 : AddMonoidAlgebra (k ⊗[k] K) ℤ ≃ₐ[k] AddMonoidAlgebra K ℤ :=
    AddMonoidAlgebra.mapAlgEquiv k ℤ e2
  have e : LaurentPolynomial k ⊗[k] K ≃ₐ[k] LaurentPolynomial K := e1.trans e3
  exact MulEquiv.isDomain (LaurentPolynomial K) e.toMulEquiv

open CategoryTheory in
theorem gm_geometricallyIntegral {k : Type*} [Field k] :
    AlgebraicGeometry.GeometricallyIntegral (Work.AbVar.Gm k).hom := by
  haveI : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme)
      (AlgebraicGeometry.IsIntegral) :=
    ⟨fun {X Y} e hX => by
      letI := hX
      exact IsIntegral.of_isIso e.hom⟩
  change GeometricallyIntegral
    (Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k))))
  rw [GeometricallyIntegral.eq_geometrically]
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  refine (ObjectProperty.prop_iff_of_iso (AlgebraicGeometry.IsIntegral)
    (pullbackSpecIso k (LaurentPolynomial k) K)).mpr ?_
  rw [affine_isIntegral_iff]
  exact isDomain_tensor_laurent k K

end Work.AbVar.TestObjects
