/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The affine model case of the Galois quotient statement

For a `k`-algebra `A` and a finite Galois extension `k'/k`, the projection
`Spec (A ⊗_k k') ⟶ Spec A` is the categorical quotient of `Spec (A ⊗_k k')` by the action of
`Gal k k'`: every invariant morphism of `k`-schemes out of `Spec (A ⊗_k k')` descends uniquely to
`Spec A`.

The proof is a descent along the finite faithfully flat morphism `Spec (A ⊗_k k') ⟶ Spec A`, using
the splitting `(A ⊗_k k') ⊗_A (A ⊗_k k') ≅ ∏_σ (A ⊗_k k')` of the kernel pair (which encodes the
invariance of the morphism under the action).
-/
import Mathlib
import Submission.Work.Descent.Basic
import Submission.Work.Descent.Scheme
import Submission.Work.Descent.QuotientSetup
import Submission.Work.Descent.galoisTensorSelfOver_bijective
import Submission.Work.Descent.flat_surjective_specMap_tensorProduct
import Submission.Work.Descent.galAct_Aff_pullbackSpecIso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
open scoped TensorProduct
open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Work.Descent.AffineModelAux

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
  [IsGalois k k']

/-- The concrete kernel pair of `Spec (algebraMap A (A ⊗_k k'))`. -/
theorem isPullback_tensorKernel (A : Type u) [CommRing A] [Algebra k A] :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A)
        (A := A ⊗[k] k') (B := A ⊗[k] k'))))
      (Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := A)
        (A := A ⊗[k] k') (B := A ⊗[k] k')).toRingHom)))
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[k] k'))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[k] k')))) := by
  refine IsPullback.of_iso
    (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[k] k'))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[k] k')))))
    (AlgebraicGeometry.pullbackSpecIso A (A ⊗[k] k') (A ⊗[k] k')) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (AlgebraicGeometry.pullbackSpecIso_hom_fst A (A ⊗[k] k') (A ⊗[k] k')).symm
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (AlgebraicGeometry.pullbackSpecIso_hom_snd A (A ⊗[k] k') (A ⊗[k] k')).symm
  · simp
  · simp

/-- `Spec (A ⊗_k k')` is the fibre product of `Spec A` and `Spec k'` over `Spec k`. -/
theorem isPullback_specTensor (A : Type u) [CommRing A] [Algebra k A] :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[k] k'))))
      (Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := k) (A := A)
        (B := k')).toRingHom)))
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (specMap k k') := by
  refine IsPullback.of_iso
    (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (specMap k k'))
    (AlgebraicGeometry.pullbackSpecIso k A k') (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (AlgebraicGeometry.pullbackSpecIso_hom_fst' k A k').symm
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (AlgebraicGeometry.pullbackSpecIso_hom_snd k A k').symm
  · simp
  · simp

/-- The kernel pair condition for the affine model, given the Galois splitting of
`B ⊗_A B` for `B = A ⊗_k k'`. -/
theorem tensorKernel_condition (A : Type u) [CommRing A] [Algebra k A] (Y : Scheme)
    (Φ : Spec (CommRingCat.of (A ⊗[k] k')) ⟶ Y)
    (hΓ : ∀ σ : Gal k k',
      Spec.map (CommRingCat.ofHom ((baseChangeAlgEquiv A σ).toRingHom)) ≫ Φ = Φ)
    (hθ : Function.Bijective (Algebra.TensorProduct.lift (galoisLeftA k k' A) (galoisRightA k k' A)
      (fun _ _ => Commute.all _ _))) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A)
        (A := A ⊗[k] k') (B := A ⊗[k] k'))) ≫ Φ
      = Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := A)
        (A := A ⊗[k] k') (B := A ⊗[k] k')).toRingHom)) ≫ Φ := by
  classical
  let θ : (A ⊗[k] k') ⊗[A] (A ⊗[k] k') ≃ₐ[A] (Gal k k' → (A ⊗[k] k')) :=
    AlgEquiv.ofBijective (Algebra.TensorProduct.lift (galoisLeftA k k' A) (galoisRightA k k' A)
      (fun _ _ => Commute.all _ _)) hθ
  -- the two ring-level component computations
  have hcomp₁ : ∀ σ : Gal k k',
      (Pi.evalRingHom (fun _ : Gal k k' => A ⊗[k] k') σ).comp (θ.toRingHom.comp
          (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A ⊗[k] k')
            (B := A ⊗[k] k'))) =
        (baseChangeAlgEquiv A σ).toRingHom := by
    intro σ
    refine RingHom.ext (fun x => ?_)
    simp [θ, AlgEquiv.ofBijective_apply, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.includeLeftRingHom_apply, galoisLeftA, galoisRightA]
  have hcomp₂ : ∀ σ : Gal k k',
      (Pi.evalRingHom (fun _ : Gal k k' => A ⊗[k] k') σ).comp (θ.toRingHom.comp
          ((Algebra.TensorProduct.includeRight (R := A) (A := A ⊗[k] k')
            (B := A ⊗[k] k')).toRingHom)) = RingHom.id (A ⊗[k] k') := by
    intro σ
    refine RingHom.ext (fun x => ?_)
    simp [θ, AlgEquiv.ofBijective_apply, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.includeRight_apply, galoisLeftA, galoisRightA]
  -- the composite `Spec (∏_σ B) ⟶ Y` in the two ways
  have key₁ : ∀ σ : Gal k k',
      Sigma.ι (fun _ : Gal k k' => Spec (CommRingCat.of (A ⊗[k] k'))) σ ≫
        (AlgebraicGeometry.sigmaSpec (fun _ : Gal k k' => CommRingCat.of (A ⊗[k] k')) ≫
          Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A)
            (A := A ⊗[k] k') (B := A ⊗[k] k'))) ≫ Φ)) = Φ := by
    intro σ
    simp only [← Category.assoc]
    rw [AlgebraicGeometry.ι_sigmaSpec]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      RingHom.comp_assoc, hcomp₁ σ]
    exact hΓ σ
  have key₂ : ∀ σ : Gal k k',
      Sigma.ι (fun _ : Gal k k' => Spec (CommRingCat.of (A ⊗[k] k'))) σ ≫
        (AlgebraicGeometry.sigmaSpec (fun _ : Gal k k' => CommRingCat.of (A ⊗[k] k')) ≫
          Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := A)
            (A := A ⊗[k] k') (B := A ⊗[k] k')).toRingHom)) ≫ Φ)) = Φ := by
    intro σ
    simp only [← Category.assoc]
    rw [AlgebraicGeometry.ι_sigmaSpec]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      RingHom.comp_assoc, hcomp₂ σ]
    rw [show CommRingCat.ofHom (RingHom.id (A ⊗[k] k')) = 𝟙 _ from rfl, Spec.map_id]
    simp
  have heq : (AlgebraicGeometry.sigmaSpec (fun _ : Gal k k' => CommRingCat.of (A ⊗[k] k')) ≫
        Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A)
          (A := A ⊗[k] k') (B := A ⊗[k] k'))) ≫ Φ))
      = (AlgebraicGeometry.sigmaSpec (fun _ : Gal k k' => CommRingCat.of (A ⊗[k] k')) ≫
        Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := A)
          (A := A ⊗[k] k') (B := A ⊗[k] k')).toRingHom)) ≫ Φ)) :=
    Sigma.hom_ext _ _ (fun σ => by rw [key₁ σ, key₂ σ])
  have h2 : Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A)
          (A := A ⊗[k] k') (B := A ⊗[k] k'))) ≫ Φ)
      = Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := A)
          (A := A ⊗[k] k') (B := A ⊗[k] k')).toRingHom)) ≫ Φ) := by
    haveI : IsIso (AlgebraicGeometry.sigmaSpec (fun _ : Gal k k' => CommRingCat.of (A ⊗[k] k'))) :=
      inferInstance
    exact (cancel_epi _).mp heq
  have h2' : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A)
        (A := A ⊗[k] k') (B := A ⊗[k] k')) ≫ CommRingCat.ofHom θ.toRingHom
      = CommRingCat.ofHom (θ.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom (R := A)
          (A := A ⊗[k] k') (B := A ⊗[k] k'))) := (CommRingCat.ofHom_comp _ _).symm
  have h2'' : CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := A)
        (A := A ⊗[k] k') (B := A ⊗[k] k')).toRingHom) ≫ CommRingCat.ofHom θ.toRingHom
      = CommRingCat.ofHom (θ.toRingHom.comp ((Algebra.TensorProduct.includeRight (R := A)
          (A := A ⊗[k] k') (B := A ⊗[k] k')).toRingHom)) := (CommRingCat.ofHom_comp _ _).symm
  have h3 : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A)
        (A := A ⊗[k] k') (B := A ⊗[k] k'))) ≫ Φ
      = Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := A)
        (A := A ⊗[k] k') (B := A ⊗[k] k')).toRingHom)) ≫ Φ := by
    haveI : IsIso (CommRingCat.ofHom θ.toRingHom) :=
      (RingEquiv.toCommRingCatIso θ.toRingEquiv).isIso_hom
    haveI : IsIso (Spec.map (CommRingCat.ofHom θ.toRingHom)) :=
      (AlgebraicGeometry.Scheme.Spec.mapIso
        (RingEquiv.toCommRingCatIso θ.toRingEquiv).op).isIso_hom
    exact (cancel_epi _).mp h2
  exact h3


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The affine model case of the Galois quotient statement. -/
theorem affineModel_isGaloisQuotient_of (A : Type u) [CommRing A] [Algebra k A]
    (hθ : Function.Bijective (Algebra.TensorProduct.lift (galoisLeftA k k' A)
      (galoisRightA k k' A) (fun _ _ => Commute.all _ _)))
    (hnat : ∀ σ : Gal k k', galAct (X := Aff k A) σ ≫
        (AlgebraicGeometry.pullbackSpecIso k A k').hom =
      (AlgebraicGeometry.pullbackSpecIso k A k').hom ≫
        Spec.map (CommRingCat.ofHom ((baseChangeAlgEquiv A σ).toRingHom)))
    (hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[k] k')))))
    (hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[k] k'))))) :
    IsGaloisQuotient k k' (Aff k A) := by
  intro Y Φ hΦ hΓ
  let e : (baseChange (k := k) (k' := k') (Aff k A)).left ≅
      Spec (CommRingCat.of (A ⊗[k] k')) := AlgebraicGeometry.pullbackSpecIso k A k'
  let Φs : Spec (CommRingCat.of (A ⊗[k] k')) ⟶ Y.left := e.inv ≫ Φ
  let πT : Spec (CommRingCat.of (A ⊗[k] k')) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[k] k')))
  have hconj : ∀ σ : Gal k k', Spec.map (CommRingCat.ofHom ((baseChangeAlgEquiv A σ).toRingHom)) ≫ e.inv =
      e.inv ≫ galAct (X := Aff k A) σ := by
    intro σ
    have h : galAct (X := Aff k A) σ ≫ e.hom =
        e.hom ≫ Spec.map (CommRingCat.ofHom ((baseChangeAlgEquiv A σ).toRingHom)) := hnat σ
    have h2 : e.inv ≫ galAct (X := Aff k A) σ =
        e.inv ≫ (galAct (X := Aff k A) σ ≫ e.hom) ≫ e.inv := by simp
    calc Spec.map (CommRingCat.ofHom ((baseChangeAlgEquiv A σ).toRingHom)) ≫ e.inv
        = e.inv ≫ (galAct (X := Aff k A) σ ≫ e.hom) ≫ e.inv := by rw [h]; simp
      _ = e.inv ≫ galAct (X := Aff k A) σ := h2.symm
  have hΓs : ∀ σ : Gal k k', Spec.map (CommRingCat.ofHom ((baseChangeAlgEquiv A σ).toRingHom)) ≫ Φs = Φs := by
    intro σ
    show Spec.map (CommRingCat.ofHom ((baseChangeAlgEquiv A σ).toRingHom)) ≫ (e.inv ≫ Φ) = e.inv ≫ Φ
    rw [← Category.assoc, hconj σ, Category.assoc, hΓ σ]
  have hcond : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A)
        (A := A ⊗[k] k') (B := A ⊗[k] k'))) ≫ Φs
      = Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := A)
        (A := A ⊗[k] k') (B := A ⊗[k] k')).toRingHom)) ≫ Φs :=
    tensorKernel_condition A Y.left Φs hΓs hθ
  haveI : Flat πT := hflat
  haveI : Surjective πT := hsurj
  haveI : IsRegularEpi πT := isRegularEpi_of_flat_of_surjective_of_isAffine _
  haveI : Epi πT := inferInstance
  obtain ⟨gs, hgs⟩ := IsRegularEpi.exists_of_isKernelPair πT
    (isPullback_tensorKernel (k := k) (k' := k') A) Φs hcond
  have hπ : baseChangeπ (k := k) (k' := k') (Aff k A) = e.hom ≫ πT :=
    (AlgebraicGeometry.pullbackSpecIso_hom_fst' k A k').symm
  have hehom : e.hom ≫ Φs = Φ := by
    simp only [Φs]
    exact e.hom_inv_id_assoc Φ
  have haux : Φs ≫ Y.hom = πT ≫ (Aff k A).hom := by
    apply (cancel_epi e.hom).mp
    calc e.hom ≫ (Φs ≫ Y.hom)
        = Φ ≫ Y.hom := by rw [← Category.assoc, hehom]
      _ = (baseChange (k := k) (k' := k') (Aff k A)).hom ≫ specMap k k' := hΦ
      _ = baseChangeπ (k := k) (k' := k') (Aff k A) ≫ (Aff k A).hom := (baseChangeπ_hom _).symm
      _ = (e.hom ≫ πT) ≫ (Aff k A).hom := by rw [hπ]
      _ = e.hom ≫ (πT ≫ (Aff k A).hom) := by rw [Category.assoc]
  have hstr : gs ≫ Y.hom = (Aff k A).hom := by
    apply (cancel_epi πT).mp
    rw [← Category.assoc, hgs, haux]
  have hmain : baseChangeπ (k := k) (k' := k') (Aff k A) ≫ gs = Φ := by
    rw [hπ, Category.assoc, hgs, hehom]
  refine ⟨Over.homMk gs hstr, ?_, ?_⟩
  · show baseChangeπ (k := k) (k' := k') (Aff k A) ≫ gs = Φ
    exact hmain
  · intro y hy
    have hyl : y.left = gs := by
      have h1 : πT ≫ y.left = πT ≫ gs := by
        apply (cancel_epi e.hom).mp
        rw [← Category.assoc, ← Category.assoc, ← hπ, hy, hmain]
      exact (cancel_epi πT).mp h1
    exact Over.OverMorphism.ext hyl

/-- The affine model case of the Galois quotient statement, with all auxiliary inputs
discharged: `Spec A` is the categorical quotient of `Spec (A ⊗_k k')` by the Galois action. -/
theorem affineModel_isGaloisQuotient (A : Type u) [CommRing A] [Algebra k A] :
    IsGaloisQuotient k k' (Aff k A) :=
  affineModel_isGaloisQuotient_of A (galoisTensorSelfOver_bijective A)
    (fun σ => galAct_Aff_pullbackSpecIso (k := k) (k' := k') A σ)
    (flat_surjective_specMap_tensorProduct (k := k) (k' := k') A).1
    (flat_surjective_specMap_tensorProduct (k := k) (k' := k') A).2

end Work.Descent.AffineModelAux
