import Mathlib
import Submission.Work.SymQuot.NormPoint.BaseChange

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `bcT` preserves symmetric tensors

The base-change map `bcT L : ⨂[F]^n Q →ₐ[F] ⨂[L]^n (L ⊗[F] Q)` intertwines the two permutation
actions (`bcT_permAlg`), hence sends symmetric tensors to symmetric tensors
(`bcT_mem_symTensors`).
-/

set_option autoImplicit false

open TensorProduct
open scoped TensorProduct

universe u

namespace Work.SymQuot.NormPoint

/-- **`bcT` intertwines the permutation actions.**  Base change of the tensor power commutes with
the reindexing of the tensor factors. -/
theorem bcT_permAlg {F : Type u} [Field F] {Q : Type u} [CommRing Q] [Algebra F Q] {n : ℕ}
    (L : Type u) [Field L] [Algebra F L] (σ : Equiv.Perm (Fin n)) (t : Tens F Q n) :
    bcT (F := F) (Q := Q) (n := n) L (permAlg (Q := Q) σ t) =
      permAlg (F := L) (Q := TensorProduct F L Q) σ (bcT (F := F) (Q := Q) (n := n) L t) := by
  let Φ : Tens F Q n →ₗ[F] Tens L (TensorProduct F L Q) n :=
    ((permAlg (F := L) (Q := TensorProduct F L Q) σ).toLinearMap.restrictScalars F).comp
      (bcT (F := F) (Q := Q) (n := n) L).toLinearMap
  let Ψ : Tens F Q n →ₗ[F] Tens L (TensorProduct F L Q) n :=
    (bcT (F := F) (Q := Q) (n := n) L).toLinearMap.comp (permAlg (Q := Q) σ).toLinearMap
  have h : Φ = Ψ := by
    apply PiTensorProduct.ext
    ext u
    simp only [LinearMap.compMultilinearMap_apply]
    change (permAlg (F := L) (Q := TensorProduct F L Q) σ)
        (bcT (F := F) (Q := Q) (n := n) L (PiTensorProduct.tprod F u)) =
      bcT (F := F) (Q := Q) (n := n) L (permAlg (Q := Q) σ (PiTensorProduct.tprod F u))
    rw [bcT_tprod, permAlg_tprod, permAlg_tprod, bcT_tprod]
  exact (DFunLike.congr_fun h t).symm

theorem bcT_mem_symTensors {F : Type u} [Field F] {Q : Type u} [CommRing Q] [Algebra F Q]
    {n : ℕ} (L : Type u) [Field L] [Algebra F L] {t : Tens F Q n}
    (ht : t ∈ symTensors F Q n) :
    bcT (F := F) (Q := Q) (n := n) L t ∈ symTensors L (TensorProduct F L Q) n := by
  rw [mem_symTensors] at ht ⊢
  intro σ
  rw [← bcT_permAlg L σ t, ht σ]

end Work.SymQuot.NormPoint
