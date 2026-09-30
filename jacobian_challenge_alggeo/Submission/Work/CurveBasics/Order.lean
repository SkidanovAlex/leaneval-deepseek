/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The principal divisor of a rational function

For a curve `C` and `h : K(C)`, the order of vanishing of `h` at a place is Mathlib's
`Scheme.ord`, and it is nonzero at only finitely many places (`finite_support_ord`), so it
can be packaged as a divisor `div h`.  This file sets that up.
-/
import Submission.Work.CurveBasics.Divisor
import Submission.Work.CurveBasics.Place.Coheight
import Submission.Work.CurveBasics.Order.finite_support_ord

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The order of vanishing of a rational function at a place. -/
abbrev ordAt (C : Curve k) (h : C.functionField) (Q : Place C) : ℤ :=
  Scheme.ord h Q.point

/-- The order of vanishing of a rational function is nonzero at only finitely many places. -/
theorem finite_support_ordAt (C : Curve k) (h : C.functionField) :
    {Q : Place C | C.ordAt h Q ≠ 0}.Finite :=
  Work.CurveBasics.Order.finite_support_ord C h

/-- The principal divisor of a rational function. -/
noncomputable def div (C : Curve k) (h : C.functionField) : Div C :=
  Finsupp.ofSupportFinite (C.ordAt h) (C.finite_support_ordAt h)

@[simp]
theorem div_apply (C : Curve k) (h : C.functionField) (Q : Place C) :
    C.div h Q = Scheme.ord h Q.point :=
  congrFun (Finsupp.ofSupportFinite_coe (f := C.ordAt h) (hf := C.finite_support_ordAt h)) Q

theorem div_coe (C : Curve k) (h : C.functionField) :
    (C.div h : Place C → ℤ) = C.ordAt h :=
  Finsupp.ofSupportFinite_coe

@[simp]
theorem div_zero (C : Curve k) : C.div 0 = 0 := by
  ext Q
  simp [div_apply]

theorem div_mul (C : Curve k) {h g : C.functionField} (hh : h ≠ 0) (hg : g ≠ 0) :
    C.div (h * g) = C.div h + C.div g := by
  ext Q
  simp only [div_apply, Finsupp.add_apply]
  exact Scheme.ord_mul hh hg

/-- The effectivity of `div h + D` written as a pointwise lower bound on `ord`. -/
theorem isEffective_div_add_iff (C : Curve k) {D : Div C} {h : C.functionField} :
    (C.div h + D).IsEffective ↔ ∀ Q, -D Q ≤ Scheme.ord h Q.point := by
  simp only [Div.IsEffective, Finsupp.add_apply, div_apply]
  constructor
  · intro hh Q; linarith [hh Q]
  · intro hh Q; linarith [hh Q]

end

end Curve

end Work.CurveBasics
