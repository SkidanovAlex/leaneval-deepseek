import Mathlib
import Submission.Work.SymQuot.NormPoint.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


universe u

namespace Work.SymQuot.NormPoint

theorem bcT_exists {F : Type u} [Field F] {Q : Type u} [CommRing Q] [Algebra F Q] {n : ℕ}
    (L : Type u) [Field L] [Algebra F L] :
    ∃ Φ : Tens F Q n →ₐ[F] Tens L (TensorProduct F L Q) n,
      ∀ u : Fin n → Q, Φ (PiTensorProduct.tprod F u) =
        PiTensorProduct.tprod L (fun j => TensorProduct.tmul F (1 : L) (u j)) := by
  -- The linear map `Q → L ⊗[F] Q`, `q ↦ 1 ⊗ q`, is the algebra map `includeRight`.
  let g : ∀ _ : Fin n, Q →ₗ[F] (TensorProduct F L Q) :=
    fun _ => (Algebra.TensorProduct.includeRight (R := F) (A := L) (B := Q)).toLinearMap
  -- The `F`-multilinear map `(u_j) ↦ ⨂_j (1 ⊗ u_j)`: the `L`-multilinear map `tprod L`
  -- restricted to `F`, composed with `includeRight` in every factor.
  let f : MultilinearMap F (fun _ : Fin n => Q) (Tens L (TensorProduct F L Q) n) :=
    (MultilinearMap.restrictScalars F
      (PiTensorProduct.tprod L : MultilinearMap L (fun _ : Fin n => TensorProduct F L Q)
        (Tens L (TensorProduct F L Q) n))).compLinearMap g
  refine ⟨PiTensorProduct.liftAlgHom f ?_ ?_, ?_⟩
  · -- `f` sends the unit to the unit.
    show f 1 = 1
    have h1 : (fun i : Fin n => (Algebra.TensorProduct.includeRight (R := F) (A := L) (B := Q))
          (1 : Q)) = (1 : Fin n → TensorProduct F L Q) := by
      funext i
      rw [Pi.one_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.one_def]
    simp only [f, MultilinearMap.compLinearMap_apply, MultilinearMap.coe_restrictScalars, g,
      AlgHom.toLinearMap_apply, Pi.one_apply]
    rw [h1, PiTensorProduct.one_def]
  · -- `f` is multiplicative on the product of the algebras `Q`.
    intro x y
    have hxy : (fun i : Fin n => (Algebra.TensorProduct.includeRight (R := F) (A := L) (B := Q))
          (x i * y i))
        = (fun i : Fin n => (Algebra.TensorProduct.includeRight (R := F) (A := L) (B := Q)) (x i) *
            (Algebra.TensorProduct.includeRight (R := F) (A := L) (B := Q)) (y i)) := by
      funext i
      rw [map_mul]
    simp only [f, MultilinearMap.compLinearMap_apply, MultilinearMap.coe_restrictScalars, g,
      AlgHom.toLinearMap_apply, Pi.mul_def]
    rw [hxy, PiTensorProduct.tprod_mul_tprod, Pi.mul_def]
  · -- Value of `Φ` on a pure tensor.
    intro u
    rw [PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod]
    simp only [f, MultilinearMap.compLinearMap_apply, MultilinearMap.coe_restrictScalars, g,
      AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeRight_apply]

end Work.SymQuot.NormPoint
