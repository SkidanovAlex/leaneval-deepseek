/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The fraction field of a domain tensored with a field extension

Let `A` be a domain which is a `k`-algebra, `K` its fraction field (as a `k`-algebra,
`IsScalarTower k A K`) and `L` a field extension of `k`.  If `A ⊗[k] L` is a domain, then
so is `K ⊗[k] L`: the latter is the localization of the former at the image of the
non-zero elements of `A`, and localizing a domain at non-zero elements again gives a
domain.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open TensorProduct
open scoped Classical

universe u

namespace Work.CurveBasics

/-- If `K` is the fraction field of a domain `A` over `k` and `A ⊗[k] L` is a domain for a
field extension `L/k`, then `K ⊗[k] L` is a domain as well. -/
theorem isDomain_tensor_of_fractionRing {k A L K : Type u} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Field L] [Algebra k L] [Field K] [Algebra k K] [Algebra A K]
    [IsScalarTower k A K] [IsFractionRing A K] (h : IsDomain (A ⊗[k] L)) :
    IsDomain (K ⊗[k] L) := by
  haveI : IsDomain (A ⊗[k] L) := h
  let f : A →ₐ[k] K := IsScalarTower.toAlgHom k A K
  letI : Algebra (A ⊗[k] L) (K ⊗[k] L) :=
    (Algebra.TensorProduct.map f (AlgHom.id k L)).toRingHom.toAlgebra
  have hH : (algebraMap (A ⊗[k] L) (K ⊗[k] L)).comp
      (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := L)).toRingHom =
      (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := L)).toRingHom := by
    ext s
    show (Algebra.TensorProduct.map f (AlgHom.id k L)) (1 ⊗ₜ[k] s) = 1 ⊗ₜ[k] s
    simp
  haveI : IsScalarTower A (A ⊗[k] L) (K ⊗[k] L) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    show (Algebra.TensorProduct.map f (AlgHom.id k L)) ((a : A) ⊗ₜ[k] (1 : L)) =
      algebraMap A K a ⊗ₜ[k] 1
    simp [f]
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[k] L) (nonZeroDivisors A))
      (K ⊗[k] L) :=
    IsLocalization.tensorProduct_tensorProduct (R := k) (S := L) (A := A)
      (M := nonZeroDivisors A) (B := K) hH
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (R := A ⊗[k] L)
    (M := Algebra.algebraMapSubmonoid (A ⊗[k] L) (nonZeroDivisors A)) (K ⊗[k] L) ?_
  simp only [Algebra.algebraMapSubmonoid]
  rintro x ⟨a, ha, rfl⟩
  simp only [mem_nonZeroDivisors_iff_ne_zero]
  intro hzero
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeLeft (R := k) (S := A) (A := A) (B := L)) :=
    Algebra.TensorProduct.includeLeft_injective (RingHom.injective (algebraMap k L))
  exact (mem_nonZeroDivisors_iff_ne_zero.mp ha)
    (hinj (by simpa [Algebra.TensorProduct.includeLeft_apply] using hzero))

end Work.CurveBasics
