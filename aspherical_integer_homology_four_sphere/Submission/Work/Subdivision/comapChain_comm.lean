import Mathlib
import Submission.Work.Subdivision.ComapChain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Subdivision

theorem comapChain_comm {C : ChainComplex (ModuleCat ℤ) ℕ} (S : Work.Subdivision.SubData C)
    (T : ∀ k, Submodule ℤ (C.X k)) (hT : ∀ k, T k ≤ S.sub k)
    (hTd : ∀ k (x : C.X (k + 1)), x ∈ T (k + 1) → (C.d (k + 1) k).hom x ∈ T k) (k : ℕ) :
    CategoryTheory.CategoryStruct.comp
      (ModuleCat.ofHom ((Submodule.comapSubtypeEquivOfLe (hT (k + 1))).toLinearMap :
        ↥((S.comapChain T hT hTd).sub (k + 1)) →ₗ[ℤ] ↥(T (k + 1))))
      ((Work.Subdivision.SubData.mk T hTd).chain.d (k + 1) k) =
    CategoryTheory.CategoryStruct.comp
      ((S.comapChain T hT hTd).chain.d (k + 1) k)
      (ModuleCat.ofHom ((Submodule.comapSubtypeEquivOfLe (hT k)).toLinearMap :
        ↥((S.comapChain T hT hTd).sub k) →ₗ[ℤ] ↥(T k))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, ChainComplex.of_d]
  simp only [LinearEquiv.coe_toLinearMap]
  rw [SubData.dL_apply (S := SubData.mk T hTd) k]
  rw [Submodule.comapSubtypeEquivOfLe_apply_coe]
  rw [Submodule.comapSubtypeEquivOfLe_apply_coe]
  rw [SubData.dL_apply (S := S.comapChain T hT hTd) k]
  simp only [ChainComplex.of_d, ModuleCat.hom_ofHom, SubData.dL_apply]

end Work.Subdivision
