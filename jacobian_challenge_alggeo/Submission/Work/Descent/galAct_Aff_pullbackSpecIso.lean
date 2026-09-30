import Mathlib
import Submission.Work.Descent.QuotientSetup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry

open scoped TensorProduct

universe u

namespace Work.Descent

/-- The Galois action on `Spec A ×_k Spec k'` is, under the canonical identification
`pullbackSpecIso k A k'` with `Spec (A ⊗[k] k')`, induced by the ring automorphism
`baseChangeAlgEquiv A σ` of `A ⊗[k] k'` acting on the second tensor factor.

Concretely: the square

```
Spec (A ⊗[k] k') --Spec(baseChangeAlgEquiv A σ)--> Spec (A ⊗[k] k')
      |                                                |
      | e.hom                                          | e.hom
      v                                                v
      P  --------------- galAct (Aff k A) σ ---------> P
```

commutes, where `P = Spec A ×_k Spec k'` and `e = pullbackSpecIso k A k'`. -/
theorem galAct_Aff_pullbackSpecIso {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (A : Type u) [CommRing A] [Algebra k A] (σ : Work.Descent.Gal k k') :
    CategoryTheory.CategoryStruct.comp (Work.Descent.galAct (Work.Descent.Aff k A) σ)
        (AlgebraicGeometry.pullbackSpecIso k A k').hom =
      CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.pullbackSpecIso k A k').hom
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          ((Work.Descent.baseChangeAlgEquiv A σ).toRingHom))) := by
  -- The two ring homomorphisms describing the action on the tensor product factors.
  have h_left : ((Work.Descent.baseChangeAlgEquiv A σ).toRingHom.comp
      (algebraMap A (A ⊗[k] k')) : A →+* (A ⊗[k] k')) = algebraMap A (A ⊗[k] k') := by
    ext a
    simp [Algebra.TensorProduct.algebraMap_apply, Work.Descent.baseChangeAlgEquiv_tmul]
  have h_right : ((Work.Descent.baseChangeAlgEquiv A σ).toRingHom.comp
        (Algebra.TensorProduct.includeRight : k' →ₐ[k] (A ⊗[k] k')).toRingHom : k' →+* (A ⊗[k] k'))
      = ((Algebra.TensorProduct.includeRight : k' →ₐ[k] (A ⊗[k] k')).toRingHom.comp
        (σ : k' →+* k')) := by
    ext c
    simp [Algebra.TensorProduct.includeRight_apply, Work.Descent.baseChangeAlgEquiv_tmul]
  -- `Spec.map` form of the two computations above.
  have hb_fst : (Spec.map (CommRingCat.ofHom ((Work.Descent.baseChangeAlgEquiv A σ).toRingHom)))
      ≫ (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[k] k'))))
      = (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[k] k')))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h_left]
  have hb_snd : (Spec.map (CommRingCat.ofHom ((Work.Descent.baseChangeAlgEquiv A σ).toRingHom)))
      ≫ (Spec.map (CommRingCat.ofHom
          ((Algebra.TensorProduct.includeRight : k' →ₐ[k] (A ⊗[k] k')).toRingHom)))
      = (Spec.map (CommRingCat.ofHom
          (((Algebra.TensorProduct.includeRight : k' →ₐ[k] (A ⊗[k] k')).toRingHom.comp
            (σ : k' →+* k'))))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h_right]
  have hsnd_map : (Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : k' →ₐ[k] (A ⊗[k] k')).toRingHom)))
      ≫ (Spec.map (CommRingCat.ofHom (σ : k' →+* k')))
      = (Spec.map (CommRingCat.ofHom
          (((Algebra.TensorProduct.includeRight : k' →ₐ[k] (A ⊗[k] k')).toRingHom.comp
            (σ : k' →+* k'))))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  -- The two projections of `pullbackSpecIso`, in both directions.
  have h_inv_fst : (pullbackSpecIso k A k').inv
      ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))
      = Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[k] k'))) :=
    pullbackSpecIso_inv_fst' k A k'
  have h_hom_fst : (pullbackSpecIso k A k').hom
      ≫ Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[k] k')))
      = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
    pullbackSpecIso_hom_fst' k A k'
  have h_inv_snd : (pullbackSpecIso k A k').inv
      ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))
      = Spec.map (CommRingCat.ofHom
          ((Algebra.TensorProduct.includeRight : k' →ₐ[k] (A ⊗[k] k')).toRingHom)) :=
    pullbackSpecIso_inv_snd k A k'
  have h_hom_snd : (pullbackSpecIso k A k').hom
      ≫ Spec.map (CommRingCat.ofHom
          ((Algebra.TensorProduct.includeRight : k' →ₐ[k] (A ⊗[k] k')).toRingHom))
      = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
    pullbackSpecIso_hom_snd k A k'
  -- The Galois action is over `X`, hence trivial on the first projection.
  have h_gal_fst : Work.Descent.galAct (Work.Descent.Aff k A) σ
      ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))
      = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
    Work.Descent.galAct_π _ σ
  -- On the second projection the Galois action is `Spec.map σ`.
  have h_gal_snd : Work.Descent.galAct (Work.Descent.Aff k A) σ
      ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))
      = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))
        ≫ Spec.map (CommRingCat.ofHom (σ : k' →+* k')) := by
    have h : Work.Descent.galAct (Work.Descent.Aff k A) σ
        ≫ (Work.Descent.baseChange (Work.Descent.Aff k A)).hom
        = (Work.Descent.baseChange (Work.Descent.Aff k A)).hom
          ≫ Spec.map (CommRingCat.ofHom (σ : k' →+* k')) := by
      simp only [Work.Descent.galAct, pullback.map, Work.Descent.baseChange_hom,
        pullback.lift_snd]
    exact h
  -- First projection: both sides of the desired identity agree.
  have hR_fst : ((pullbackSpecIso k A k').hom
        ≫ (Spec.map (CommRingCat.ofHom ((Work.Descent.baseChangeAlgEquiv A σ).toRingHom)))
        ≫ (pullbackSpecIso k A k').inv)
      ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))
      = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))) := by
    rw [Category.assoc, Category.assoc, h_inv_fst, hb_fst, h_hom_fst]
  have hL_snd : Work.Descent.galAct (Work.Descent.Aff k A) σ
      ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))
      = (pullbackSpecIso k A k').hom
        ≫ Spec.map (CommRingCat.ofHom
          (((Algebra.TensorProduct.includeRight : k' →ₐ[k] (A ⊗[k] k')).toRingHom.comp
            (σ : k' →+* k')))) := by
    rw [h_gal_snd, ← h_hom_snd, Category.assoc, hsnd_map]
  have hR_snd : ((pullbackSpecIso k A k').hom
        ≫ (Spec.map (CommRingCat.ofHom ((Work.Descent.baseChangeAlgEquiv A σ).toRingHom)))
        ≫ (pullbackSpecIso k A k').inv)
      ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))
      = (pullbackSpecIso k A k').hom
        ≫ Spec.map (CommRingCat.ofHom
          (((Algebra.TensorProduct.includeRight : k' →ₐ[k] (A ⊗[k] k')).toRingHom.comp
            (σ : k' →+* k')))) := by
    rw [Category.assoc, Category.assoc, h_inv_snd, hb_snd]
  -- The action is determined by its two projections.
  have key : Work.Descent.galAct (Work.Descent.Aff k A) σ
      = (pullbackSpecIso k A k').hom
        ≫ (Spec.map (CommRingCat.ofHom ((Work.Descent.baseChangeAlgEquiv A σ).toRingHom)))
        ≫ (pullbackSpecIso k A k').inv := by
    apply pullback.hom_ext (f := (Work.Descent.Aff k A).hom) (g := Work.Descent.specMap k k')
    · exact h_gal_fst.trans hR_fst.symm
    · exact hL_snd.trans hR_snd.symm
  have h1 : Work.Descent.galAct (Work.Descent.Aff k A) σ ≫ (pullbackSpecIso k A k').hom
      = ((pullbackSpecIso k A k').hom
        ≫ (Spec.map (CommRingCat.ofHom ((Work.Descent.baseChangeAlgEquiv A σ).toRingHom)))
        ≫ (pullbackSpecIso k A k').inv) ≫ (pullbackSpecIso k A k').hom :=
    congrArg (fun t => t ≫ (pullbackSpecIso k A k').hom) key
  have h2 : ((pullbackSpecIso k A k').hom
        ≫ (Spec.map (CommRingCat.ofHom ((Work.Descent.baseChangeAlgEquiv A σ).toRingHom)))
        ≫ (pullbackSpecIso k A k').inv) ≫ (pullbackSpecIso k A k').hom
      = (pullbackSpecIso k A k').hom
        ≫ (Spec.map (CommRingCat.ofHom ((Work.Descent.baseChangeAlgEquiv A σ).toRingHom))) := by
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact h1.trans h2

end Work.Descent
