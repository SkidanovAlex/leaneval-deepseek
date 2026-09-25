import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open scoped TensorProduct

/-
# Base change preserves dimension over fields

`Module.Finite` over the field `K`, `L ⊗[K] F` is a finite-dimensional vector
space over `F` (with `F` acting on the right tensor factor), of dimension
`Module.finrank K L`.

The right factor action is the algebra structure
`Algebra.TensorProduct.rightAlgebra : Algebra F (L ⊗[K] F)`, which Mathlib
keeps out of the global instance set (to avoid diamonds); we activate it
locally in this file.
-/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Commons.LinearAlgebra.Dimension

/-- The canonical flip `L ⊗[K] F ≅ F ⊗[K] L` is `F`-linear, where `F` acts on
the right factor of the source and on the left factor of the target. -/
lemma comm_smul {K L F : Type*} [CommSemiring K] [CommSemiring L] [CommSemiring F]
    [Algebra K L] [Algebra K F] (f : F) :
    ∀ x : L ⊗[K] F,
      (Algebra.TensorProduct.comm K L F) (f • x) =
        f • (Algebra.TensorProduct.comm K L F) x := by
  intro x
  refine TensorProduct.inductionOn x ?tmul ?add
  · intro l x0
    have hdom : f • (l ⊗ₜ[K] x0) = l ⊗ₜ[K] (f • x0) := by
      rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul]
      simp [one_mul, smul_eq_mul]
    rw [hdom]
    rw [Algebra.TensorProduct.comm_tmul]
    rw [show f • (Algebra.TensorProduct.comm K L F) (l ⊗ₜ[K] x0) =
          f • (x0 ⊗ₜ[K] l) by
          rw [Algebra.TensorProduct.comm_tmul]]
    rw [TensorProduct.smul_tmul']
  · intro x y hx hy
    have hL : (Algebra.TensorProduct.comm K L F) (f • (x + y)) =
        (Algebra.TensorProduct.comm K L F) (f • x) +
          (Algebra.TensorProduct.comm K L F) (f • y) := by
      rw [smul_add, map_add]
    have hR : f • ((Algebra.TensorProduct.comm K L F) (x + y)) =
        f • (Algebra.TensorProduct.comm K L F) x +
          f • (Algebra.TensorProduct.comm K L F) y := by
      rw [map_add, TensorProduct.smul_add]
    rw [hL, hR]
    rw [hx, hy]

/-- The flip `L ⊗[K] F ≃ₗ[F] F ⊗[K] L`, `F` acting on the right factor of the
source and on the left factor of the target. -/
noncomputable def flipRight (K L F : Type*) [CommSemiring K] [CommSemiring L] [CommSemiring F]
    [Algebra K L] [Algebra K F] : (L ⊗[K] F) ≃ₗ[F] (F ⊗[K] L) where
  toFun x := (Algebra.TensorProduct.comm K L F : L ⊗[K] F → F ⊗[K] L) x
  invFun x := ((Algebra.TensorProduct.comm K L F).symm : F ⊗[K] L → L ⊗[K] F) x
  left_inv := by intro x; simp
  right_inv := by intro x; simp
  map_add' := by intro x y; simp [map_add]
  map_smul' := by
    intro f
    exact comm_smul f

theorem tensor_field_baseChange_finrank {K L F : Type*} [Field K] [Field L]
    [Algebra K L] [Field F] [Algebra K F] [Module.Finite K L] :
    Module.finrank F (L ⊗[K] F) = Module.finrank K L := by
  calc
    Module.finrank F (L ⊗[K] F) = Module.finrank F (F ⊗[K] L) :=
      (flipRight K L F).finrank_eq
    _ = Module.finrank K L := by
      exact Module.finrank_baseChange (R := F) (S := K) (M' := L)

end Commons.LinearAlgebra.Dimension