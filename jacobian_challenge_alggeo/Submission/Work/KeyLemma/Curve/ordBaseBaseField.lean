/-
# The canonical algebra structure `k[h] ⊆ k(h)`

Mathlib's `Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean` provides, in the *scoped*
namespace `IntermediateField.algebraAdjoinAdjoin`, the canonical `Algebra` structure
`Algebra ↥(Algebra.adjoin F S) ↥(IntermediateField.adjoin F S)` together with
`IsScalarTower` and `IsFractionRing` instances.  Because those instances are *scoped*, any
statement about `↥(C.ordBase h) = k[h]` and `↥(baseField C h) = k(h)` that is written without
opening the scope would quantify over an *arbitrary* (and possibly non-canonical) algebra
structure on `↥(C.ordBase h) → ↥(baseField C h)` -- which makes such statements unprovable and,
worse, meaningless (the `k`-algebra map `k[h] → k(h)` could be `h ↦ h²`).

This file re-exports the three instances as *global* instances specialised to
`A = C.ordBase h`, `K = baseField C h` (they are definitionally the scoped ones, so importing
this file together with the scope open causes no diamond in practice).
-/
import Mathlib
import Submission.Work.KeyLemma.Curve.genericSum
import Submission.Work.CurveBasics.Order.ordPosSetup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits
open scoped Classical

universe u

namespace Work.KeyLemma.Curve

/-- The canonical inclusion `k[h] ⊆ k(h)`. -/
noncomputable instance instAlgebraOrdBaseBaseField (k : Type u) [Field k]
    (C : Work.CurveBasics.Curve k) (h : C.functionField) :
    Algebra ↥(C.ordBase h) ↥(baseField C h) :=
  (Subalgebra.inclusion
    (IntermediateField.algebra_adjoin_le_adjoin k ({h} : Set C.functionField))).toRingHom.toAlgebra

/-- The canonical inclusion `k[h] ⊆ k(h)` is a `k`-algebra map. -/
instance instIsScalarTowerOrdBaseBaseField (k : Type u) [Field k]
    (C : Work.CurveBasics.Curve k) (h : C.functionField) :
    IsScalarTower k ↥(C.ordBase h) ↥(baseField C h) :=
  Subalgebra.inclusion.isScalarTower_left
    (IntermediateField.algebra_adjoin_le_adjoin k ({h} : Set C.functionField)) _

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- `k(h)` is the fraction field of `k[h]`. -/
instance instIsFractionRingOrdBaseBaseField (k : Type u) [Field k]
    (C : Work.CurveBasics.Curve k) (h : C.functionField) :
    IsFractionRing ↥(C.ordBase h) ↥(baseField C h) := inferInstance

/-- `k[h] → k(h)` is the inclusion. -/
@[simp]
theorem algebraMap_ordBase_baseField (k : Type u) [Field k]
    (C : Work.CurveBasics.Curve k) (h : C.functionField) (x : ↥(C.ordBase h)) :
    ((algebraMap ↥(C.ordBase h) ↥(baseField C h) x : ↥(baseField C h)) : C.functionField)
      = (x : C.functionField) := rfl

variable {k : Type u} [Field k]

/-- `k(h⁻¹) = k(h)`: the base field of a rational function is its base field at `∞`. -/
theorem baseField_inv (C : Work.CurveBasics.Curve k) {h : C.functionField} (hh : h ≠ 0) :
    baseField C h⁻¹ = baseField C h := by
  have h1 : h ∈ baseField C h⁻¹ := by
    have h2 : h⁻¹ ∈ baseField C h⁻¹ :=
      IntermediateField.subset_adjoin k _ (Set.mem_singleton h⁻¹)
    have h3 : (h⁻¹)⁻¹ ∈ baseField C h⁻¹ := IntermediateField.inv_mem _ h2
    simpa using h3
  refine le_antisymm ?_ ?_
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact IntermediateField.inv_mem _ (IntermediateField.subset_adjoin k _ (Set.mem_singleton h))
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h1

end Work.KeyLemma.Curve
