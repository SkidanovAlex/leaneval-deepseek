import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.TestObjects

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `𝔸¹` is geometrically integral over the base field

`Work.AbVar.Ga k = Spec k[X]` with its structure morphism to `Spec k`.  It is the
prototype of a morphism which is geometrically integral but *not* proper, so it is
one of the test objects for the rigidity lemma: the rigidity statement has to use
properness in an essential way, and `𝔸¹` shows that the corresponding statement for
arbitrary geometrically integral group schemes fails.

The substance of the proof: for a field extension `k ⊆ K`, the base change of
`Spec k[X] → Spec k` along `Spec K → Spec k` is `Spec (k[X] ⊗[k] K)`, and
`k[X] ⊗[k] K ≃ K[X]` is a polynomial ring over a field, hence a domain.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Work.AbVar.TestObjects

/-- For a field extension `k ⊆ K`, the base change `k[X] ⊗[k] K` of the polynomial
algebra `k[X]` is again a polynomial algebra (over `K`), in particular a domain. -/
theorem polynomial_tensor_isDomain (k : Type u) [Field k] (K : Type u) [Field K]
    [Algebra k K] : IsDomain (TensorProduct k (Polynomial k) K) :=
  MulEquiv.isDomain (Polynomial K)
    ((Algebra.TensorProduct.comm k (Polynomial k) K).trans (polyEquivTensor k K).symm).toMulEquiv

/-- `𝔸¹_k = Spec k[X]` is geometrically integral over `Spec k`. -/
theorem ga_specMap_geometricallyIntegral {k : Type u} [Field k] :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) := by
  rw [GeometricallyIntegral.eq_geometrically, geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  exact @IsIntegral.of_isIso (Spec (CommRingCat.of (TensorProduct k (Polynomial k) K))) Y
    ((affine_isIntegral_iff _).mpr (polynomial_tensor_isDomain k K))
    (h.isoPullback ≪≫ pullbackSpecIso k (Polynomial k) K).inv inferInstance

open CategoryTheory in
theorem ga_geometricallyIntegral {k : Type*} [Field k] :
    AlgebraicGeometry.GeometricallyIntegral (Work.AbVar.Ga k).hom := by
  have hf : (Work.AbVar.Ga k).hom
      = Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) := rfl
  rw [hf]
  exact ga_specMap_geometricallyIntegral

end Work.AbVar.TestObjects
