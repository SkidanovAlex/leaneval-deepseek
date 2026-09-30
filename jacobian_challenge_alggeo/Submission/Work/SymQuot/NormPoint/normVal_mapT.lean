/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Invariance of the norm functional under the tensor power of an algebra equivalence
(area SY, NP6)

For an `F`-algebra equivalence `e : Q ≃ₐ[F] Q'`, the induced algebra equivalence
`mapT e : ⨂[F]^n Q ≃ₐ[F] ⨂[F]^n Q'` of the `n`-fold tensor powers (sending
`u₀ ⊗ … ⊗ u_{n-1}` to `e u₀ ⊗ … ⊗ e u_{n-1}`) transports the norm functional: computing
`normVal` in the transported basis `v.map e.toLinearEquiv` after applying `mapT e` gives the
same value as computing `normVal` in the basis `v`.

The engine is `detT_mapT`: the determinant functional `detT (v.map e)`, precomposed with
`mapT e`, equals `detT v`.  Both are `F`-linear, so it suffices to check the identity on pure
tensors (`PiTensorProduct.ext`), where it is `Basis.det_map` together with
`detT_tprod`.
-/
import Mathlib
import Submission.Work.SymQuot.NormPoint.MapT

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

variable {F : Type u} [Field F] {Q Q' : Type u} [CommRing Q] [Algebra F Q]
  [CommRing Q'] [Algebra F Q'] {n : ℕ}

/-- `mapT e` sends the `n`-fold tensor power of the basis `v` of `Q` to that of the transported
basis `v.map e.toLinearEquiv` of `Q'`. -/
theorem tprod_mapT_basis (e : Q ≃ₐ[F] Q') (v : Module.Basis (Fin n) F Q) :
    PiTensorProduct.tprod F (⇑(v.map e.toLinearEquiv)) =
      mapT e (PiTensorProduct.tprod F v) := by
  rw [mapT_tprod]
  congr 1

/-- **Transport of the determinant functional along `mapT`.**  In the transported basis
`v.map e.toLinearEquiv` of `Q'`, the determinant functional evaluated on `mapT e t` is the
determinant functional of `t` in the basis `v`. -/
theorem detT_mapT (e : Q ≃ₐ[F] Q') (v : Module.Basis (Fin n) F Q) (t : Tens F Q n) :
    detT (v.map e.toLinearEquiv) (mapT e t) = detT v t := by
  have key : (detT (v.map e.toLinearEquiv)).comp (mapT e).toLinearMap = detT v := by
    apply PiTensorProduct.ext
    ext f
    change detT (v.map e.toLinearEquiv) (mapT e (PiTensorProduct.tprod F f)) =
      detT v (PiTensorProduct.tprod F f)
    rw [mapT_tprod, detT_tprod, detT_tprod, Module.Basis.det_map]
    congr 1
    funext i
    simp
  exact LinearMap.congr_fun key t

/-- **Invariance of the norm functional under `mapT`.** — the `n`-th tensor power of an
`F`-algebra equivalence `e` intertwines the norm functionals attached to a basis `v` of `Q`
and to its image `v.map e.toLinearEquiv` in `Q'`. -/
theorem normVal_mapT {F : Type u} [Field F] {Q Q' : Type u} [CommRing Q] [Algebra F Q]
    [CommRing Q'] [Algebra F Q'] {n : ℕ} (e : Q ≃ₐ[F] Q') (v : Module.Basis (Fin n) F Q)
    (t : Tens F Q n) :
    normVal (v.map e.toLinearEquiv) (mapT e t) = normVal v t := by
  show detT (v.map e.toLinearEquiv)
      (mapT e t * PiTensorProduct.tprod F (v.map e.toLinearEquiv)) =
    detT v (t * PiTensorProduct.tprod F v)
  rw [tprod_mapT_basis e v,
    (map_mul (mapT e) t (PiTensorProduct.tprod F v)).symm,
    detT_mapT]

end Work.SymQuot.NormPoint
