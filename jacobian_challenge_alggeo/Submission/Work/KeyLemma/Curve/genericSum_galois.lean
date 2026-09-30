import Mathlib
import Submission.Work.KeyLemma.Curve.genericSum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.KeyLemma.Curve

open CategoryTheory AlgebraicGeometry Limits
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

universe u

theorem genericSum_galois {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (h : C.functionField)
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A] (f : C.toOver ⟶ A)
    (N : Type u) [Field N] [Algebra ↥(Work.KeyLemma.Curve.baseField C h) N] [Algebra k N]
    [IsScalarTower k ↥(Work.KeyLemma.Curve.baseField C h) N]
    [FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField]
    (τ : N ≃ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N) :
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      Work.KeyLemma.Curve.genericSum (C := C) (h := h) (N := N) f
    = Work.KeyLemma.Curve.genericSum (C := C) (h := h) (N := N) f := by
  -- `Spec.map τ`, viewed as an automorphism `specOver N ⟶ specOver N` in the over-category.
  let galOver : specOver (k := k) N ⟶ specOver (k := k) N :=
    Over.homMk (Spec.map (CommRingCat.ofHom τ.toRingHom)) (by
      simp only [specOver, Over.mk_hom]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext x
      simp only [RingHom.comp_apply]
      rw [IsScalarTower.algebraMap_apply k ↥(Work.KeyLemma.Curve.baseField C h) N]
      exact AlgEquiv.commutes τ (algebraMap k ↥(Work.KeyLemma.Curve.baseField C h) x))
  -- `galOver` sends the conjugate point attached to `σ` to the one attached to `τ.comp σ`.
  have hconj : ∀ σ : ↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N,
      galOver ≫ conjPtOver C h f N σ
        = conjPtOver C h f N ((τ : N →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N).comp σ) := by
    intro σ
    have hmap : Spec.map (CommRingCat.ofHom ((τ : N →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N).comp σ).toRingHom)
        = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    ext
    simp only [Over.comp_left, Over.homMk_left, galOver, conjPt]
    rw [hmap]
    simp only [Category.assoc]
  -- the reindexing bijection `σ ↦ τ.comp σ` of the set of `K`-embeddings
  let conjEquiv : (↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N) ≃
      (↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N) :=
    { toFun := fun σ => (τ : N →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N).comp σ
      invFun := fun σ => ((τ.symm : N ≃ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N) :
        N →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N).comp σ
      left_inv := by intro σ; ext x; simp [AlgHom.comp_apply]
      right_inv := by intro σ; ext x; simp [AlgHom.comp_apply] }
  -- `galOver` fixes the product, since it permutes the factors
  have hprod : galOver ≫ genericSumOver C h f N = genericSumOver C h f N := by
    let phi : (specOver (k := k) N ⟶ A) →* (specOver (k := k) N ⟶ A) :=
      { toFun := fun g => galOver ≫ g
        map_one' := MonObj.comp_one galOver
        map_mul' := fun a b => MonObj.comp_mul galOver a b }
    calc galOver ≫ genericSumOver C h f N
        = phi (∏ σ : ↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N,
            conjPtOver C h f N σ) := rfl
      _ = ∏ σ : ↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N,
            phi (conjPtOver C h f N σ) := map_prod phi _ Finset.univ
      _ = ∏ σ : ↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N,
            conjPtOver C h f N (conjEquiv σ) := by
            refine Fintype.prod_congr _ _ (fun σ => ?_)
            show galOver ≫ conjPtOver C h f N σ = conjPtOver C h f N (conjEquiv σ)
            exact hconj σ
      _ = ∏ σ : ↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N,
            conjPtOver C h f N σ :=
            Fintype.prod_equiv conjEquiv _ _ (fun σ => rfl)
      _ = genericSumOver C h f N := rfl
  have key := congrArg Over.Hom.left hprod
  rw [Over.comp_left] at key
  simpa only [galOver, Over.homMk_left, genericSum] using key

end Work.KeyLemma.Curve
