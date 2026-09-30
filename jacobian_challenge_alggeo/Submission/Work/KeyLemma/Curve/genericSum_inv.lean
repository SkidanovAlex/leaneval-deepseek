import Mathlib
import Submission.Work.KeyLemma.Curve.genericSum
import Submission.Work.KeyLemma.Curve.ordBaseBaseField

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.KeyLemma.Curve

universe u

set_option synthInstance.maxHeartbeats 800000
open CategoryTheory AlgebraicGeometry Limits
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

/-- **The generic-fibre sum is unchanged when the pencil coordinate `h` is replaced by `h⁻¹`.**

The generic-fibre sum of the pencil of `h` is the product over the `K`-embeddings `E →ₐ[K] N`
(with `K = k(h)`, `E = K(C)`) of the corresponding conjugate points of `C`; replacing `h` by
`h⁻¹` gives the *same* pencil (only the coordinate on `ℙ¹` is inverted), hence the same multiset
of points, hence the same product.  This is the formal bookkeeping that allows the second end of
the pencil to be computed by the same specialisation statement as the first one.

`baseField C h⁻¹ = baseField C h` (`Work.KeyLemma.Curve.baseField_inv`) as subfields of `E`, but
the two `Algebra ↥(baseField C ·) N` structures on `N` are independent hypotheses.  The
hypothesis `hcomp` pins them to each other: it is the compatibility of the two `algebraMap`s with
the canonical identification of `↥(baseField C h)` and `↥(baseField C h⁻¹)` with their common
image in `E = K(C)`.  (For the instances arising in practice, namely
`algebraMap ↥(baseField C h) N = algebraMap ↥C.functionField N ∘ inclusion` and the same with
`h⁻¹`, `hcomp` holds by construction.)  Under `hcomp` the two index types of the products are
identified by the identity on the underlying field maps `E → N`, and the products agree termwise
because `conjPtOver σ` depends only on `σ.toRingHom`; use `Fintype.prod_equiv` as in
`Work.KeyLemma.Curve.genericSum_galois`. -/
theorem genericSum_inv {k : Type u} [Field k] {C : Work.CurveBasics.Curve k}
    {h : C.functionField} (hh : h ≠ 0)
    {N : Type u} [Field N] [Algebra k N]
    [Algebra ↥(Work.KeyLemma.Curve.baseField C h) N]
    [IsScalarTower k ↥(Work.KeyLemma.Curve.baseField C h) N]
    [FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField]
    [Algebra ↥(Work.KeyLemma.Curve.baseField C h⁻¹) N]
    [IsScalarTower k ↥(Work.KeyLemma.Curve.baseField C h⁻¹) N]
    [FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h⁻¹) ↥C.functionField]
    (hcomp : ∀ (x : ↥(Work.KeyLemma.Curve.baseField C h))
      (y : ↥(Work.KeyLemma.Curve.baseField C h⁻¹)),
      (x : C.functionField) = (y : C.functionField) →
        algebraMap ↥(Work.KeyLemma.Curve.baseField C h) N x =
          algebraMap ↥(Work.KeyLemma.Curve.baseField C h⁻¹) N y)
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    (f : C.toOver ⟶ A) :
    Work.KeyLemma.Curve.genericSum (C := C) (h := h⁻¹) (N := N) f =
      Work.KeyLemma.Curve.genericSum (C := C) (h := h) (N := N) f := by
  -- `k(h⁻¹) = k(h)`, as subfields of `E = K(C)`.
  have hbase : Work.KeyLemma.Curve.baseField C h⁻¹ = Work.KeyLemma.Curve.baseField C h :=
    Work.KeyLemma.Curve.baseField_inv C hh
  -- The two index types of the products are identified by the identity on the underlying
  -- field maps `E → N`; `hcomp` is exactly what makes this well defined.
  let e : (↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h⁻¹)] N) ≃
      (↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N) :=
  { toFun := fun σ => AlgHom.mk σ.toRingHom (fun x => by
      have hx : (x : C.functionField) ∈ Work.KeyLemma.Curve.baseField C h⁻¹ := by
        rw [hbase]; exact x.2
      let y : ↥(Work.KeyLemma.Curve.baseField C h⁻¹) := ⟨(x : C.functionField), hx⟩
      have hy : (x : C.functionField) = (y : C.functionField) := rfl
      rw [hcomp x y hy]
      exact σ.commutes y)
    invFun := fun τ => AlgHom.mk τ.toRingHom (fun y => by
      have hy : (y : C.functionField) ∈ Work.KeyLemma.Curve.baseField C h := by
        rw [← hbase]; exact y.2
      let x : ↥(Work.KeyLemma.Curve.baseField C h) := ⟨(y : C.functionField), hy⟩
      have hxy : (x : C.functionField) = (y : C.functionField) := rfl
      rw [← hcomp x y hxy]
      exact τ.commutes x)
    left_inv := fun σ => by ext x; rfl
    right_inv := fun τ => by ext x; rfl }
  -- `conjPtOver σ` depends only on `σ.toRingHom`, so the two conjugates agree.
  have hterm : ∀ σ : ↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h⁻¹)] N,
      Work.KeyLemma.Curve.conjPtOver (C := C) (h := h⁻¹) (N := N) f σ =
        Work.KeyLemma.Curve.conjPtOver (C := C) (h := h) (N := N) f (e σ) := by
    intro σ
    apply CategoryTheory.Over.OverMorphism.ext
    simp only [Work.KeyLemma.Curve.conjPtOver, CategoryTheory.Over.homMk_left,
      Work.KeyLemma.Curve.conjPt]
  -- hence the two products agree.
  have hprod : Work.KeyLemma.Curve.genericSumOver (C := C) (h := h⁻¹) (N := N) f =
      Work.KeyLemma.Curve.genericSumOver (C := C) (h := h) (N := N) f := by
    show (∏ σ : ↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h⁻¹)] N,
        Work.KeyLemma.Curve.conjPtOver (C := C) (h := h⁻¹) (N := N) f σ)
      = (∏ σ : ↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N,
        Work.KeyLemma.Curve.conjPtOver (C := C) (h := h) (N := N) f σ)
    exact Fintype.prod_equiv e _ _ hterm
  exact congrArg CategoryTheory.Over.Hom.left hprod

end Work.KeyLemma.Curve
