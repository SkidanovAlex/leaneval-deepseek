/-
# The second end of the pencil: the generic value for the coordinate `h⁻¹`

For the specialisation at `∞` of the pencil of `h` the branch argument is run again with the
coordinate `u = h⁻¹` (so that `posPart C u = negPart C h`), but with the *same* field `N` as for
the first end.  Since `k(h⁻¹) = k(h)`, the field `N` (a finite Galois extension of `k(h)`) is also
a finite Galois extension of `k(h⁻¹)` for the composite `k(h⁻¹) → K(C) → N` (see
`BranchInv.Transfer`), so that the generic value of the branch product is again
`genericSum (h := h)`: this is `Work.KeyLemma.Curve.genericSum_inv`.
-/
import Mathlib
import Submission.Work.KeyLemma.Curve.BranchInv.Transfer
import Submission.Work.KeyLemma.Curve.genericSum_inv
import Submission.Work.CurveBasics.Order.finiteDimensional_adjoin_functionField

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry Limits
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

universe u

namespace Work.KeyLemma.Curve

open Work.CurveBasics

variable {k : Type u} [Field k]

/-- The inverse of a transcendental element is transcendental. -/
theorem transcendental_inv {C : Curve k} {h : C.functionField} (hh : Transcendental k h) :
    Transcendental k h⁻¹ := fun halg => hh (by simpa using IsAlgebraic.inv halg)

/-- The elementwise form of the `k`-linearity of the composite `k(h)`-algebra structure on `N`. -/
theorem algebraMap_k_eq_of_comp {C : Curve k} {h : C.functionField}
    {N : Type u} [Field N] [Algebra k N] [Algebra ↥(baseField C h) N]
    [Algebra ↥C.functionField N]
    (hkK : ∀ x : k,
      algebraMap k N x = algebraMap ↥(baseField C h) N (algebraMap k ↥(baseField C h) x))
    (hKE : (algebraMap ↥(baseField C h) N)
      = (algebraMap ↥C.functionField N).comp (algebraMap ↥(baseField C h) ↥C.functionField))
    (x : k) :
    algebraMap k N x = algebraMap ↥C.functionField N (algebraMap k ↥C.functionField x) := by
  rw [hkK x, hKE, RingHom.comp_apply]
  exact congrArg (algebraMap ↥C.functionField N)
    (IsScalarTower.algebraMap_apply k ↥(baseField C h) ↥C.functionField x)

/-- **The generic value of the second end.**  With the same field `N` as for the first end and the
composite `k(h⁻¹)`-algebra structure on it, the generic-fibre sum of the pencil of `h⁻¹` is the
generic-fibre sum of the pencil of `h`.

This is `Work.KeyLemma.Curve.genericSum_inv` restated so that the two algebra structures on `N`
can be the ones arising in the second end (the `k(h⁻¹)`-structure being the composite through
`K(C)`); the hypothesis `hcomp` pins them to each other, and holds by construction there. -/
theorem genericSum_inv_comp {C : Curve k} {h : C.functionField} (hh : h ≠ 0)
    {N : Type u} [Field N] [Algebra ↥(baseField C h) N] [Algebra k N]
    [IsScalarTower k ↥(baseField C h) N]
    [Algebra ↥(baseField C h⁻¹) N] [IsScalarTower k ↥(baseField C h⁻¹) N]
    [Algebra ↥C.functionField N]
    [FiniteDimensional ↥(baseField C h) ↥C.functionField]
    [FiniteDimensional ↥(baseField C h⁻¹) ↥C.functionField]
    (hcomp : ∀ (x : ↥(baseField C h)) (y : ↥(baseField C h⁻¹)),
      (x : C.functionField) = (y : C.functionField) →
        algebraMap ↥(baseField C h) N x = algebraMap ↥(baseField C h⁻¹) N y)
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsCommMonObj A]
    (f : C.toOver ⟶ A) :
    genericSum (C := C) (h := h⁻¹) (N := N) f = genericSum (C := C) (h := h) (N := N) f := by
  -- the two index types are identified by the identity on the underlying field maps `K(C) → N`
  let e : (↥C.functionField →ₐ[↥(baseField C h⁻¹)] N) ≃
      (↥C.functionField →ₐ[↥(baseField C h)] N) :=
  { toFun := fun σ => AlgHom.mk σ.toRingHom (fun x => by
      have hx : (x : C.functionField) ∈ baseField C h⁻¹ := by
        rw [baseField_inv C hh]; exact x.2
      let y : ↥(baseField C h⁻¹) := ⟨(x : C.functionField), hx⟩
      have hy : (x : C.functionField) = (y : C.functionField) := rfl
      show σ.toRingHom (x : C.functionField) = algebraMap ↥(baseField C h) N x
      rw [hcomp x y hy]
      exact σ.commutes y)
    invFun := fun τ => AlgHom.mk τ.toRingHom (fun y => by
      have hy : (y : C.functionField) ∈ baseField C h := by
        rw [← baseField_inv C hh]; exact y.2
      let x : ↥(baseField C h) := ⟨(y : C.functionField), hy⟩
      have hxy : (x : C.functionField) = (y : C.functionField) := rfl
      show τ.toRingHom (y : C.functionField) = algebraMap ↥(baseField C h⁻¹) N y
      rw [← hcomp x y hxy]
      exact τ.commutes x)
    left_inv := fun σ => by ext x; rfl
    right_inv := fun τ => by ext x; rfl }
  -- `conjPtOver σ` depends only on `σ.toRingHom`, so the two conjugates agree
  have hterm : ∀ σ : ↥C.functionField →ₐ[↥(baseField C h⁻¹)] N,
      conjPtOver (C := C) (h := h⁻¹) (N := N) f σ
        = conjPtOver (C := C) (h := h) (N := N) f (e σ) := by
    intro σ
    apply CategoryTheory.Over.OverMorphism.ext
    simp only [conjPtOver, CategoryTheory.Over.homMk_left, conjPt]
  have hprod : genericSumOver (C := C) (h := h⁻¹) (N := N) f
      = genericSumOver (C := C) (h := h) (N := N) f := by
    show (∏ σ : ↥C.functionField →ₐ[↥(baseField C h⁻¹)] N,
        conjPtOver (C := C) (h := h⁻¹) (N := N) f σ)
      = (∏ σ : ↥C.functionField →ₐ[↥(baseField C h)] N,
        conjPtOver (C := C) (h := h) (N := N) f σ)
    exact Fintype.prod_equiv e _ _ hterm
  exact congrArg CategoryTheory.Over.Hom.left hprod

end Work.KeyLemma.Curve
