/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tensoring the sections of a geometrically integral morphism with a field

If `f : X ⟶ Spec k` is geometrically integral (in particular geometrically irreducible and
geometrically reduced) and `i : Spec A ⟶ X` is an open immersion whose image sits over
`Spec k` via `Spec.map (algebraMap k A)`, then for every field extension `L/k` the
tensor product `A ⊗[k] L` is a domain.

The reason is that `Spec (A ⊗[k] L)` is isomorphic to the open subscheme
`pullback (i ≫ f) (Spec L)` of the integral scheme `pullback f (Spec L)`.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open scoped Classical

universe u

namespace Work.CurveBasics

/-- If `f : X ⟶ Spec k` is geometrically integral and `i : Spec A ⟶ X` is an open immersion
with `i ≫ f = Spec.map (algebraMap k A)`, then `A ⊗[k] L` is a domain for every field
extension `L` of `k`. -/
theorem isDomain_tensor_of_isOpenImmersion {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [GeometricallyIntegral f]
    {A : Type u} [CommRing A] [Algebra k A] [Nontrivial A]
    (i : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion i]
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (L : Type u) [Field L] [Algebra k L] : IsDomain (A ⊗[k] L) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap k L)) with hg
  have hInt : IsIntegral (pullback f g) :=
    (GeometricallyIntegral.geometrically_isIntegral (f := f))
      (Z := pullback f g) g (pullback.fst f g) (pullback.snd f g) (IsPullback.of_hasPullback f g)
  haveI : Nontrivial (A ⊗[k] L) :=
    Function.Injective.nontrivial (Algebra.TensorProduct.includeLeft_injective (R := k) (S := k)
      (A := A) (B := L) (RingHom.injective (algebraMap k L)))
  obtain ⟨a⟩ : Nonempty (Spec (CommRingCat.of (A ⊗[k] L))) := inferInstance
  haveI hne : Nonempty (show Scheme.{u} from
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) g) :=
    ⟨(pullbackSpecIso k A L).inv a⟩
  haveI hne2 : Nonempty (show Scheme.{u} from pullback (i ≫ f) g) := by rw [hi]; exact hne
  let φ : pullback (i ≫ f) g ⟶ pullback f g :=
    pullback.map (i ≫ f) g f g i (𝟙 _) (𝟙 _) (by simp) (by simp)
  haveI hopen : IsOpenImmersion φ :=
    Scheme.pullback_map_isOpenImmersion (i ≫ f) g f g i (𝟙 _) (𝟙 _) (by simp) (by simp)
  haveI hOpen : IsIntegral (pullback (i ≫ f) g) := isIntegral_of_isOpenImmersion φ
  haveI hOpen' : IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) g) := by
    rw [← hi]; exact hOpen
  have hSpec : IsIntegral (Spec (CommRingCat.of (A ⊗[k] L))) :=
    IsIntegral.of_isIso (pullbackSpecIso k A L).hom
  exact (affine_isIntegral_iff (CommRingCat.of (A ⊗[k] L))).mp hSpec

end Work.CurveBasics
