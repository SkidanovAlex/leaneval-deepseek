/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The tensor power of an algebra equivalence (area SY, NP6)

For an `F`-algebra equivalence `e : Q ≃ₐ[F] Q'` and `n : ℕ`, the induced `F`-algebra
equivalence `mapT e : ⨂[F]^n Q ≃ₐ[F] ⨂[F]^n Q'` of the `n`-fold tensor powers, sending
`u₀ ⊗ … ⊗ u_{n-1}` to `e u₀ ⊗ … ⊗ e u_{n-1}`.  It intertwines the permutation actions
(`mapT_permAlg`), hence preserves symmetric tensors (`mapT_mem_symTensors`); the invariance of
the norm functional under it is `Work.SymQuot.NormPoint.normVal_mapT`.
-/
import Mathlib
import Submission.Work.SymQuot.NormPoint.NormPoint

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

/-- The underlying linear equivalence of `mapT e`. -/
noncomputable def mapTLin (e : Q ≃ₐ[F] Q') : Tens F Q n ≃ₗ[F] Tens F Q' n :=
  PiTensorProduct.congr (fun _ : Fin n => e.toLinearEquiv)

@[simp]
theorem mapTLin_tprod (e : Q ≃ₐ[F] Q') (u : Fin n → Q) :
    mapTLin e (PiTensorProduct.tprod F u) = PiTensorProduct.tprod F (fun j => e (u j)) :=
  PiTensorProduct.congr_tprod (fun _ : Fin n => e.toLinearEquiv) u

theorem mapTLin_one (e : Q ≃ₐ[F] Q') : mapTLin e (1 : Tens F Q n) = 1 := by
  rw [PiTensorProduct.one_def, mapTLin_tprod, PiTensorProduct.one_def]
  congr 1
  funext i
  simp

theorem mapTLin_mul (e : Q ≃ₐ[F] Q') (x y : Tens F Q n) :
    mapTLin e (x * y) = mapTLin e x * mapTLin e y := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s g =>
      rw [PiTensorProduct.smul_tprod_mul_smul_tprod]
      simp only [map_smul, mapTLin_tprod, Pi.mul_def]
      rw [show (fun j => e (f j * g j)) = (fun j => e (f j)) * (fun j => e (g j)) from
        funext fun j => map_mul e _ _,
        ← PiTensorProduct.smul_tprod_mul_smul_tprod]
    | add y z hy hz => simp only [mul_add, map_add, hy, hz]
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]

/-- **The tensor power of an algebra equivalence**: `mapT e` sends `u₀ ⊗ … ⊗ u_{n-1}` to
`e u₀ ⊗ … ⊗ e u_{n-1}`. -/
noncomputable def mapT (e : Q ≃ₐ[F] Q') : Tens F Q n ≃ₐ[F] Tens F Q' n :=
  AlgEquiv.ofLinearEquiv (mapTLin e) (mapTLin_one e) (mapTLin_mul e)

@[simp]
theorem mapT_tprod (e : Q ≃ₐ[F] Q') (u : Fin n → Q) :
    mapT e (PiTensorProduct.tprod F u) = PiTensorProduct.tprod F (fun j => e (u j)) :=
  mapTLin_tprod e u

/-- `mapT e` intertwines the permutation actions on the two tensor powers. -/
theorem mapT_permAlg (e : Q ≃ₐ[F] Q') (σ : Equiv.Perm (Fin n)) (t : Tens F Q n) :
    mapT e (permAlg (Q := Q) σ t) = permAlg (Q := Q') σ (mapT e t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r f => simp only [map_smul, permAlg_tprod, mapT_tprod]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `mapT e` preserves the symmetric tensors. -/
theorem mapT_mem_symTensors (e : Q ≃ₐ[F] Q') {t : Tens F Q n}
    (ht : t ∈ symTensors F Q n) : mapT e t ∈ symTensors F Q' n := by
  rw [mem_symTensors] at ht ⊢
  intro σ
  rw [← mapT_permAlg e σ t, ht σ]

end Work.SymQuot.NormPoint
