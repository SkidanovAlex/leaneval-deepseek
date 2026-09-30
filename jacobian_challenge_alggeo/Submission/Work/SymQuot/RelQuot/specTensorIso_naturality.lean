import Mathlib
import Submission.Work.SymQuot.RelQuot.relativeQuotAffinePieceAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option maxHeartbeats 1000000

universe u

/-!
# Naturality of the identification `Spec A ⊗ Spec B ≅ Spec (A ⊗[K] B)`

The main result of this file, `Work.SymQuot.RelQuot.specTensorIso_naturality`, is the naturality
in `(A, B)` of the isomorphism `specTensorIso` of `relativeQuotAffinePieceAux.lean`: for
`K`-algebra homomorphisms `φ : A₁ →ₐ[K] A₂` and `ψ : B₁ →ₐ[K] B₂`, the square

```
Spec A₂ ⊗ Spec B₂ -- Spec φ ⊗ₘ Spec ψ --> Spec A₁ ⊗ Spec B₁
      |  specTensorIso A₂ B₂                    |  specTensorIso A₁ B₁
      v                                         v
 Spec (A₂ ⊗[K] B₂) -- Spec (φ ⊗[K] ψ) --> Spec (A₁ ⊗[K] B₁)
```

commutes in the category `Over (Spec K)` of `K`-schemes.

The proof reduces (via `Over.OverMorphism.ext`, then `specTensorIso_hom_left`, which identifies
`specTensorIso` with `AlgebraicGeometry.pullbackSpecIso`) to the corresponding statement about
`pullbackSpecIso` in the category of schemes, which is checked on the two pullback projections.
The two auxiliary lemmas below are the "projection level" identities, encoding the fact that
`a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b` are natural in the pair of algebras.
-/

namespace Work.SymQuot.RelQuot

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

/-- The first projection `S ⊗[K] T → S` (i.e. `includeLeftRingHom`) is natural in the pair of
`K`-algebras: the square

```
  A₁ -- φ ------> A₂
  |                |
  a ↦ a ⊗ 1        a ↦ a ⊗ 1
  v                v
 A₁ ⊗ B₁ -- map φ ψ --> A₂ ⊗ B₂
```

commutes, hence the corresponding square of spectra commutes. -/
theorem specMap_map_includeLeftRingHom {K : Type u} [Field K] {A₁ A₂ B₁ B₂ : Type u}
    [CommRing A₁] [Algebra K A₁] [CommRing A₂] [Algebra K A₂] [CommRing B₁] [Algebra K B₁]
    [CommRing B₂] [Algebra K B₂] (φ : A₁ →ₐ[K] A₂) (ψ : B₁ →ₐ[K] B₂) :
    Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ ψ : A₁ ⊗[K] B₁ →+* A₂ ⊗[K] B₂)) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : A₁ →+* A₁ ⊗[K] B₁))
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : A₂ →+* A₂ ⊗[K] B₂)) ≫
        Spec.map (CommRingCat.ofHom (φ : A₁ →+* A₂)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom (Algebra.TensorProduct.map_comp_includeLeftRingHom φ ψ))

/-- The second projection `S ⊗[K] T → T` (i.e. `includeRight`) is natural in the pair of
`K`-algebras, hence the corresponding square of spectra commutes. -/
theorem specMap_map_includeRight {K : Type u} [Field K] {A₁ A₂ B₁ B₂ : Type u}
    [CommRing A₁] [Algebra K A₁] [CommRing A₂] [Algebra K A₂] [CommRing B₁] [Algebra K B₁]
    [CommRing B₂] [Algebra K B₂] (φ : A₁ →ₐ[K] A₂) (ψ : B₁ →ₐ[K] B₂) :
    Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ ψ : A₁ ⊗[K] B₁ →+* A₂ ⊗[K] B₂)) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight.toRingHom : B₁ →+* A₁ ⊗[K] B₁))
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight.toRingHom : B₂ →+* A₂ ⊗[K] B₂)) ≫
        Spec.map (CommRingCat.ofHom (ψ : B₁ →+* B₂)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom
      (congrArg AlgHom.toRingHom (Algebra.TensorProduct.map_comp_includeRight φ ψ)))

open CategoryTheory Limits AlgebraicGeometry in
open scoped TensorProduct MonoidalCategory in
theorem specTensorIso_naturality {K : Type u} [Field K] {A₁ A₂ B₁ B₂ : Type u}
    [CommRing A₁] [Algebra K A₁] [CommRing A₂] [Algebra K A₂] [CommRing B₁] [Algebra K B₁]
    [CommRing B₂] [Algebra K B₂] (φ : A₁ →ₐ[K] A₂) (ψ : B₁ →ₐ[K] B₂) :
    (Work.SpecLin.specOfMap φ ⊗ₘ Work.SpecLin.specOfMap ψ) ≫
        (Work.SymQuot.RelQuot.specTensorIso (K := K) A₁ B₁).hom
      = (Work.SymQuot.RelQuot.specTensorIso (K := K) A₂ B₂).hom ≫
        Work.SpecLin.specOfMap (Algebra.TensorProduct.map φ ψ) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Work.SymQuot.RelQuot.specTensorIso_hom_left]
  refine (cancel_mono (pullbackSpecIso K A₁ B₁).inv).mp ?_
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine pullback.hom_ext (f := Spec.map (CommRingCat.ofHom (algebraMap K A₁)))
    (g := Spec.map (CommRingCat.ofHom (algebraMap K B₁))) ?_ ?_
  case refine_1 =>
    calc Over.Hom.left (Work.SpecLin.specOfMap φ ⊗ₘ Work.SpecLin.specOfMap ψ) ≫
          pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K A₁)))
            (Spec.map (CommRingCat.ofHom (algebraMap K B₁)))
        = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K A₂)))
              (Spec.map (CommRingCat.ofHom (algebraMap K B₂))) ≫
            Spec.map (CommRingCat.ofHom φ.toRingHom) :=
          Over.tensorHom_left_fst _ _
            (Work.SpecLin.specOfMap φ) (Work.SpecLin.specOfMap ψ)
      _ = ((pullbackSpecIso K A₂ B₂).hom ≫ Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeLeftRingHom : A₂ →+* A₂ ⊗[K] B₂))) ≫
            Spec.map (CommRingCat.ofHom φ.toRingHom) :=
          (congrArg (fun x => x ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
            (pullbackSpecIso_hom_fst K A₂ B₂)).symm
      _ = (pullbackSpecIso K A₂ B₂).hom ≫ (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeLeftRingHom : A₂ →+* A₂ ⊗[K] B₂)) ≫
            Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
          Category.assoc _ _ _
      _ = (pullbackSpecIso K A₂ B₂).hom ≫ (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.map φ ψ : A₁ ⊗[K] B₁ →+* A₂ ⊗[K] B₂)) ≫
            Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeLeftRingHom : A₁ →+* A₁ ⊗[K] B₁))) :=
          congrArg (fun x => (pullbackSpecIso K A₂ B₂).hom ≫ x)
            (specMap_map_includeLeftRingHom φ ψ).symm
      _ = (pullbackSpecIso K A₂ B₂).hom ≫ (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.map φ ψ : A₁ ⊗[K] B₁ →+* A₂ ⊗[K] B₂)) ≫
            (pullbackSpecIso K A₁ B₁).inv ≫ pullback.fst
              (Spec.map (CommRingCat.ofHom (algebraMap K A₁)))
              (Spec.map (CommRingCat.ofHom (algebraMap K B₁)))) :=
          congrArg (fun x => (pullbackSpecIso K A₂ B₂).hom ≫ x)
            (congrArg (fun x => Spec.map (CommRingCat.ofHom
                (Algebra.TensorProduct.map φ ψ : A₁ ⊗[K] B₁ →+* A₂ ⊗[K] B₂)) ≫ x)
              (pullbackSpecIso_inv_fst K A₁ B₁).symm)
      _ = ((pullbackSpecIso K A₂ B₂).hom ≫ (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.map φ ψ : A₁ ⊗[K] B₁ →+* A₂ ⊗[K] B₂)) ≫
            (pullbackSpecIso K A₁ B₁).inv)) ≫ pullback.fst
              (Spec.map (CommRingCat.ofHom (algebraMap K A₁)))
              (Spec.map (CommRingCat.ofHom (algebraMap K B₁))) :=
          (Category.assoc _ _ _).symm
  case refine_2 =>
    calc Over.Hom.left (Work.SpecLin.specOfMap φ ⊗ₘ Work.SpecLin.specOfMap ψ) ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K A₁)))
            (Spec.map (CommRingCat.ofHom (algebraMap K B₁)))
        = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K A₂)))
              (Spec.map (CommRingCat.ofHom (algebraMap K B₂))) ≫
            Spec.map (CommRingCat.ofHom ψ.toRingHom) :=
          Over.tensorHom_left_snd _ _
            (Work.SpecLin.specOfMap φ) (Work.SpecLin.specOfMap ψ)
      _ = ((pullbackSpecIso K A₂ B₂).hom ≫ Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeRight.toRingHom : B₂ →+* A₂ ⊗[K] B₂))) ≫
            Spec.map (CommRingCat.ofHom ψ.toRingHom) :=
          (congrArg (fun x => x ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom))
            (pullbackSpecIso_hom_snd K A₂ B₂)).symm
      _ = (pullbackSpecIso K A₂ B₂).hom ≫ (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeRight.toRingHom : B₂ →+* A₂ ⊗[K] B₂)) ≫
            Spec.map (CommRingCat.ofHom ψ.toRingHom)) :=
          Category.assoc _ _ _
      _ = (pullbackSpecIso K A₂ B₂).hom ≫ (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.map φ ψ : A₁ ⊗[K] B₁ →+* A₂ ⊗[K] B₂)) ≫
            Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeRight.toRingHom : B₁ →+* A₁ ⊗[K] B₁))) :=
          congrArg (fun x => (pullbackSpecIso K A₂ B₂).hom ≫ x)
            (specMap_map_includeRight φ ψ).symm
      _ = (pullbackSpecIso K A₂ B₂).hom ≫ (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.map φ ψ : A₁ ⊗[K] B₁ →+* A₂ ⊗[K] B₂)) ≫
            (pullbackSpecIso K A₁ B₁).inv ≫ pullback.snd
              (Spec.map (CommRingCat.ofHom (algebraMap K A₁)))
              (Spec.map (CommRingCat.ofHom (algebraMap K B₁)))) :=
          congrArg (fun x => (pullbackSpecIso K A₂ B₂).hom ≫ x)
            (congrArg (fun x => Spec.map (CommRingCat.ofHom
                (Algebra.TensorProduct.map φ ψ : A₁ ⊗[K] B₁ →+* A₂ ⊗[K] B₂)) ≫ x)
              (pullbackSpecIso_inv_snd K A₁ B₁).symm)
      _ = ((pullbackSpecIso K A₂ B₂).hom ≫ (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.map φ ψ : A₁ ⊗[K] B₁ →+* A₂ ⊗[K] B₂)) ≫
            (pullbackSpecIso K A₁ B₁).inv)) ≫ pullback.snd
              (Spec.map (CommRingCat.ofHom (algebraMap K A₁)))
              (Spec.map (CommRingCat.ofHom (algebraMap K B₁))) :=
          (Category.assoc _ _ _).symm

end Work.SymQuot.RelQuot
