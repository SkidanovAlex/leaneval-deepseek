/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The pasting isomorphism of base changes of a curve along an isomorphism of fields

Let `C` be a curve over a field `K`, let `φ : L ≃ₐ[K] L'` be an isomorphism of field
extensions of `K`.  The base changes `C_L = C ×_K Spec L` and `C_{L'} = C ×_K Spec L'` are
canonically isomorphic: the square

```
C_{L'}  ⟶  C_L
  ↓         ↓
Spec L' ⟶ Spec L
```

is cartesian (pasting of two pullback squares, since `Spec L' ⟶ Spec L ⟶ Spec K` is the
structure map of `L'`).  This file constructs the isomorphism `pastingIso φ` explicitly by
the universal property of the pullback, together with its two defining projections.
-/
import Mathlib
import Submission.Work.CurveBasics.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Work.SpecLin.Alt

open Work.CurveBasics

section Pasting

variable {K : Type u} [Field K] {C : Curve K}
variable {L L' : Type u} [Field L] [Field L'] [Algebra K L] [Algebra K L']

/-- The morphism `Spec L' ⟶ Spec L` induced by `φ`, followed by `Spec L ⟶ Spec K`, is the
structure morphism `Spec L' ⟶ Spec K`. -/
lemma specMap_factor (φ : L ≃ₐ[K] L') :
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫ Curve.specMap K L = Curve.specMap K L' := by
  have h : (CommRingCat.ofHom (algebraMap K L)) ≫ (CommRingCat.ofHom φ.toRingHom)
      = CommRingCat.ofHom (algebraMap K L') := by
    rw [← CommRingCat.ofHom_comp]; congr 1; exact RingHom.ext (fun k => φ.commutes k)
  rw [Curve.specMap, Curve.specMap, ← Spec.map_comp, h]

/-- The compatibility of the two projections of the pasting square. -/
lemma pastingHom_condition (φ : L ≃ₐ[K] L') :
    Curve.baseChangeFst C L' ≫ C.hom
      = (Curve.baseChangeHom C L' ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫
          Curve.specMap K L := by
  rw [Category.assoc, specMap_factor φ]; exact pullback.condition

/-- The morphism `C_{L'} ⟶ C_L` of the pasting isomorphism. -/
noncomputable def pastingHom (φ : L ≃ₐ[K] L') :
    Curve.baseChangeLeft C L' ⟶ Curve.baseChangeLeft C L :=
  pullback.lift (Curve.baseChangeFst C L')
    (Curve.baseChangeHom C L' ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    (pastingHom_condition φ)

/-- The compatibility of the two projections of the pasting square, in the other direction. -/
lemma pastingInv_condition (φ : L ≃ₐ[K] L') :
    Curve.baseChangeFst C L ≫ C.hom
      = (Curve.baseChangeHom C L ≫ Spec.map (CommRingCat.ofHom φ.symm.toRingHom)) ≫
          Curve.specMap K L' := by
  rw [Category.assoc, specMap_factor φ.symm]; exact pullback.condition

/-- The morphism `C_L ⟶ C_{L'}` of the pasting isomorphism. -/
noncomputable def pastingInv (φ : L ≃ₐ[K] L') :
    Curve.baseChangeLeft C L ⟶ Curve.baseChangeLeft C L' :=
  pullback.lift (Curve.baseChangeFst C L)
    (Curve.baseChangeHom C L ≫ Spec.map (CommRingCat.ofHom φ.symm.toRingHom))
    (pastingInv_condition φ)

@[simp] lemma pastingHom_fst (φ : L ≃ₐ[K] L') :
    pastingHom (C := C) φ ≫ Curve.baseChangeFst C L = Curve.baseChangeFst C L' :=
  pullback.lift_fst _ _ _

@[simp] lemma pastingHom_snd (φ : L ≃ₐ[K] L') :
    pastingHom (C := C) φ ≫ Curve.baseChangeHom C L
      = Curve.baseChangeHom C L' ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) :=
  pullback.lift_snd _ _ _

@[simp] lemma pastingInv_fst (φ : L ≃ₐ[K] L') :
    pastingInv (C := C) φ ≫ Curve.baseChangeFst C L' = Curve.baseChangeFst C L :=
  pullback.lift_fst _ _ _

@[simp] lemma pastingInv_snd (φ : L ≃ₐ[K] L') :
    pastingInv (C := C) φ ≫ Curve.baseChangeHom C L'
      = Curve.baseChangeHom C L ≫ Spec.map (CommRingCat.ofHom φ.symm.toRingHom) :=
  pullback.lift_snd _ _ _

lemma spec_algEquiv_comp_inv (φ : L ≃ₐ[K] L') :
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫ (Spec.map (CommRingCat.ofHom φ.symm.toRingHom))
      = 𝟙 (Spec (CommRingCat.of L')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : φ.toRingHom.comp φ.symm.toRingHom = RingHom.id L' := by
    ext x; exact φ.apply_symm_apply x
  rw [h]; simp

lemma spec_algEquiv_inv_comp (φ : L ≃ₐ[K] L') :
    (Spec.map (CommRingCat.ofHom φ.symm.toRingHom)) ≫ (Spec.map (CommRingCat.ofHom φ.toRingHom))
      = 𝟙 (Spec (CommRingCat.of L)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : φ.symm.toRingHom.comp φ.toRingHom = RingHom.id L := by
    ext x; exact φ.symm_apply_apply x
  rw [h]; simp

lemma pastingHom_pastingInv (φ : L ≃ₐ[K] L') :
    pastingHom (C := C) φ ≫ pastingInv (C := C) φ = 𝟙 _ := by
  apply pullback.hom_ext
  · have h : (pastingHom (C := C) φ ≫ pastingInv (C := C) φ) ≫ Curve.baseChangeFst C L'
        = Curve.baseChangeFst C L' := by
      rw [Category.assoc, pastingInv_fst, pastingHom_fst]
    simpa using h
  · have h : (pastingHom (C := C) φ ≫ pastingInv (C := C) φ) ≫ Curve.baseChangeHom C L'
        = Curve.baseChangeHom C L' := by
      calc (pastingHom (C := C) φ ≫ pastingInv (C := C) φ) ≫ Curve.baseChangeHom C L'
          = pastingHom (C := C) φ ≫ (pastingInv (C := C) φ ≫ Curve.baseChangeHom C L') :=
            Category.assoc _ _ _
        _ = pastingHom (C := C) φ ≫ (Curve.baseChangeHom C L ≫
              Spec.map (CommRingCat.ofHom φ.symm.toRingHom)) := by rw [pastingInv_snd]
        _ = (pastingHom (C := C) φ ≫ Curve.baseChangeHom C L) ≫
              Spec.map (CommRingCat.ofHom φ.symm.toRingHom) := (Category.assoc _ _ _).symm
        _ = (Curve.baseChangeHom C L' ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫
              Spec.map (CommRingCat.ofHom φ.symm.toRingHom) := by rw [pastingHom_snd]
        _ = Curve.baseChangeHom C L' ≫ (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
              Spec.map (CommRingCat.ofHom φ.symm.toRingHom)) := Category.assoc _ _ _
        _ = Curve.baseChangeHom C L' ≫ 𝟙 _ := by rw [spec_algEquiv_comp_inv φ]
        _ = Curve.baseChangeHom C L' := Category.comp_id _
    simpa using h

lemma pastingInv_pastingHom (φ : L ≃ₐ[K] L') :
    pastingInv (C := C) φ ≫ pastingHom (C := C) φ = 𝟙 _ := by
  apply pullback.hom_ext
  · have h : (pastingInv (C := C) φ ≫ pastingHom (C := C) φ) ≫ Curve.baseChangeFst C L
        = Curve.baseChangeFst C L := by
      rw [Category.assoc, pastingHom_fst, pastingInv_fst]
    simpa using h
  · have h : (pastingInv (C := C) φ ≫ pastingHom (C := C) φ) ≫ Curve.baseChangeHom C L
        = Curve.baseChangeHom C L := by
      calc (pastingInv (C := C) φ ≫ pastingHom (C := C) φ) ≫ Curve.baseChangeHom C L
          = pastingInv (C := C) φ ≫ (pastingHom (C := C) φ ≫ Curve.baseChangeHom C L) :=
            Category.assoc _ _ _
        _ = pastingInv (C := C) φ ≫ (Curve.baseChangeHom C L' ≫
              Spec.map (CommRingCat.ofHom φ.toRingHom)) := by rw [pastingHom_snd]
        _ = (pastingInv (C := C) φ ≫ Curve.baseChangeHom C L') ≫
              Spec.map (CommRingCat.ofHom φ.toRingHom) := (Category.assoc _ _ _).symm
        _ = (Curve.baseChangeHom C L ≫ Spec.map (CommRingCat.ofHom φ.symm.toRingHom)) ≫
              Spec.map (CommRingCat.ofHom φ.toRingHom) := by rw [pastingInv_snd]
        _ = Curve.baseChangeHom C L ≫ (Spec.map (CommRingCat.ofHom φ.symm.toRingHom) ≫
              Spec.map (CommRingCat.ofHom φ.toRingHom)) := Category.assoc _ _ _
        _ = Curve.baseChangeHom C L ≫ 𝟙 _ := by rw [spec_algEquiv_inv_comp φ]
        _ = Curve.baseChangeHom C L := Category.comp_id _
    simpa using h

/-- **The pasting isomorphism** of the base changes of a curve along an isomorphism of field
extensions of `K`. -/
noncomputable def pastingIso (φ : L ≃ₐ[K] L') :
    Curve.baseChangeLeft C L' ≅ Curve.baseChangeLeft C L :=
  { hom := pastingHom (C := C) φ
    inv := pastingInv (C := C) φ
    hom_inv_id := pastingHom_pastingInv φ
    inv_hom_id := pastingInv_pastingHom φ }

end Pasting

end Work.SpecLin.Alt
