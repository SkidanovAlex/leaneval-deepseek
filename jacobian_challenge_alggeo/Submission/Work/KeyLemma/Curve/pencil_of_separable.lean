/-
# The separable case of the pencil statement: the wiring

This file is the *bookkeeping* file for the separable case of the pencil statement
(`Work.KeyLemma.Curve.sumOfPoints_eq_of_separable`, proved in
`Submission/Work/KeyLemma/Curve/sumOfPoints_eq_of_separable.lean`).

The reduction of the separable case to the two ingredients

* `Work.KeyLemma.Curve.exists_const_eq_genericSum` (the Galois descent of the generic-fibre sum,
  made constant by `Curve.p1Const`), and
* `Work.KeyLemma.Curve.exists_branch_sum_fixed` (the specialisation of the pencil at a zero of `h`)

together with `Work.KeyLemma.Curve.sumOfPoints_eq_of_branch` (separatedness of `A`) and
`Work.KeyLemma.Curve.genericSum_inv` (the second end, at infinity) is described in
`Submission/Work/KeyLemma/Curve/NOTES_pencil.md` §14.2 and §15, and a complete draft of the proof
is kept at `Submission/Work/KeyLemma/Curve/_mine/wiring_skeleton.txt`.

§15.2 of the notes explains the typeclass-instance trap which is the only obstacle: for subobjects
`S ⊆ T ⊆ K(C)`, an `IsScalarTower ↥S ↥T N` hypothesis is a tautology in Lean (typeclass search
resolves the `SMul`s through the ambient actions of the subtypes), and -- worse -- the instances
chosen when *elaborating a binder* (the ambient `instSMulSubtypeMem`/`instModuleSubtypeMem`) differ
from those chosen in *goals* (the canonical `Algebra.toSMul`/`Algebra.toModule`), so applications of
`exists_branch_sum_fixed` are rejected unless the type and all its instances agree syntactically.
The recommended fix is a *concrete* Galois closure (`Polynomial.SplittingField` of the minimal
polynomial of a primitive element of `K(C)/k(h)`) with *global* instances.
-/
import Mathlib
import Submission.Work.KeyLemma.Basic
import Submission.Work.CurveBasics.Basic
import Submission.Work.CurveBasics.Order

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits
open scoped Classical

universe u

namespace Work.KeyLemma.Curve

open Work.CurveBasics

variable {k : Type u} [Field k]

/-- The divisor of poles of `h` is the divisor of zeros of `h⁻¹`. -/
theorem negPart_eq_posPart_inv (C : Curve k) {h : C.functionField} (hh : h ≠ 0) :
    negPart C h = posPart C h⁻¹ := by
  ext Q
  rw [negPart_apply, posPart_apply]
  have h1 : C.ordAt h⁻¹ Q = - C.ordAt h Q := by
    have h2 := congrFun (congrArg DFunLike.coe (Work.CurveBasics.Order.div_inv C hh)) Q
    simpa [Curve.div_apply] using h2
  rw [h1]

end Work.KeyLemma.Curve
