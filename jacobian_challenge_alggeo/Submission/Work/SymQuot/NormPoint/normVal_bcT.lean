/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Base change of the norm functional (area SY, contract item 3, NP5)

For a field extension `F → L` and a commutative `F`-algebra `Q`, the base change
`bcT L : ⨂[F]^n Q →ₐ[F] ⨂[L]^n (L ⊗[F] Q)`, `tprod u ↦ tprod (1 ⊗ u_j)`, intertwines the norm
functionals: `normVal` computed with the base-changed basis `Algebra.TensorProduct.basis L v`
after base change equals `algebraMap F L` of `normVal` computed with `v`.

The engine is the computation `L ⊗[F] Q` of the determinant: in the basis
`B := Algebra.TensorProduct.basis L v` (whose `j`-th vector is `1 ⊗ₜ v j`), the matrix of the
family `(1 ⊗ₜ u j)_j` is the entrywise image under `algebraMap F L` of the matrix of `(u j)_j` in
the basis `v`; taking determinants and using that `algebraMap F L` is a ring homomorphism
(`RingHom.map_det`) gives the result.
-/
import Mathlib
import Submission.Work.SymQuot.NormPoint.BaseChange

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open TensorProduct
open scoped TensorProduct

universe u

namespace Work.SymQuot.NormPoint

variable {F : Type u} [Field F] {Q : Type u} [CommRing Q] [Algebra F Q] {n : ℕ}

/-- **Base change of the determinant functional on pure tensors.**  In the base-changed basis
`B = Algebra.TensorProduct.basis L v` of `L ⊗[F] Q`, the determinant form of a pure tensor
`tprod (1 ⊗ u_j)` is the image under `algebraMap F L` of the determinant form of `u` in the
basis `v`.  This is the matrix computation: `B.repr (1 ⊗ u j)` has `i`-th coefficient
`algebraMap F L ((v.repr (u j)) i)` (`Algebra.TensorProduct.basis_repr_tmul`), so that
`B.toMatrix (1 ⊗ u ·)` is the entrywise image of `v.toMatrix u`. -/
theorem detT_bcT_aux_tprod (L : Type u) [Field L] [Algebra F L] (v : Module.Basis (Fin n) F Q)
    (u : Fin n → Q) :
    detT (Algebra.TensorProduct.basis L v)
        (bcT (F := F) (Q := Q) (n := n) L (PiTensorProduct.tprod F u)) =
      algebraMap F L (detT v (PiTensorProduct.tprod F u)) := by
  rw [bcT_tprod]
  simp only [detT, PiTensorProduct.lift.tprod]
  have hmat : (Algebra.TensorProduct.basis L v).toMatrix (fun j => (1 : L) ⊗ₜ[F] u j)
      = (algebraMap F L).mapMatrix (v.toMatrix u) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Module.Basis.toMatrix_apply, Algebra.TensorProduct.basis_repr_tmul, one_smul,
      Finsupp.mapRange_apply]
  calc (Algebra.TensorProduct.basis L v).det (fun j => (1 : L) ⊗ₜ[F] u j)
      = ((Algebra.TensorProduct.basis L v).toMatrix (fun j => (1 : L) ⊗ₜ[F] u j)).det :=
        Module.Basis.det_apply _ _
    _ = ((algebraMap F L).mapMatrix (v.toMatrix u)).det := by rw [hmat]
    _ = algebraMap F L ((v.toMatrix u).det) :=
        (RingHom.map_det (algebraMap F L) (v.toMatrix u)).symm
    _ = algebraMap F L (v.det u) := by rw [Module.Basis.det_apply]

/-- **Base change of the determinant functional.**  For every `w`, the determinant functional
computed in the base-changed basis after base change is `algebraMap F L` of the determinant
functional of `w`.  Both sides are `F`-linear in `w`, so it suffices to check the identity on
pure tensors (`PiTensorProduct.ext`), which is `detT_bcT_aux_tprod`. -/
theorem detT_bcT (L : Type u) [Field L] [Algebra F L] (v : Module.Basis (Fin n) F Q)
    (w : Tens F Q n) :
    detT (Algebra.TensorProduct.basis L v) (bcT (F := F) (Q := Q) (n := n) L w) =
      algebraMap F L (detT v w) := by
  have key : ((detT (Algebra.TensorProduct.basis L v)).restrictScalars F).comp
        (bcT (F := F) (Q := Q) (n := n) L).toLinearMap
      = (Algebra.linearMap F L).comp (detT v) := by
    apply PiTensorProduct.ext
    ext u
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, Algebra.linearMap_apply]
    exact detT_bcT_aux_tprod L v u
  exact DFunLike.congr_fun key w

/-- **NP5.**  Base change of the norm functional: computing `normVal` after base change with the
base-changed basis `Algebra.TensorProduct.basis L v` gives `algebraMap F L` of `normVal v`.

The `L`-tensor power of `1 ⊗ v_j` is `bcT (tprod v)`, so `bcT t * tprod (basis L v)` is
`bcT (t * tprod v)` and `detT_bcT` finishes. -/
theorem normVal_bcT {F : Type u} [Field F] {Q : Type u} [CommRing Q] [Algebra F Q] {n : ℕ}
    (L : Type u) [Field L] [Algebra F L] (v : Module.Basis (Fin n) F Q) (t : Tens F Q n) :
    normVal (Algebra.TensorProduct.basis L v) (bcT (F := F) (Q := Q) (n := n) L t) =
      algebraMap F L (normVal v t) := by
  have htprod : (PiTensorProduct.tprod L) (⇑(Algebra.TensorProduct.basis L v))
      = bcT (F := F) (Q := Q) (n := n) L (PiTensorProduct.tprod F v) := by
    rw [bcT_tprod]
    congr 1
    funext j
    rw [Algebra.TensorProduct.basis_apply]
  calc normVal (Algebra.TensorProduct.basis L v) (bcT (F := F) (Q := Q) (n := n) L t)
      = detT (Algebra.TensorProduct.basis L v)
          (bcT (F := F) (Q := Q) (n := n) L t *
            PiTensorProduct.tprod L (⇑(Algebra.TensorProduct.basis L v))) := rfl
    _ = detT (Algebra.TensorProduct.basis L v)
          (bcT (F := F) (Q := Q) (n := n) L t *
            bcT (F := F) (Q := Q) (n := n) L (PiTensorProduct.tprod F v)) := by rw [htprod]
    _ = detT (Algebra.TensorProduct.basis L v)
          (bcT (F := F) (Q := Q) (n := n) L (t * PiTensorProduct.tprod F v)) := by
          rw [← map_mul]
    _ = algebraMap F L (detT v (t * PiTensorProduct.tprod F v)) := detT_bcT L v _
    _ = algebraMap F L (normVal v t) := rfl

end Work.SymQuot.NormPoint
