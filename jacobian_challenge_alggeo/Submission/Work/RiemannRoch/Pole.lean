/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR: pole divisors

The pole divisor of a rational function `x`: the effective divisor `Σ_Q max 0 (-ord_Q x) Q`.
This is the divisor used in the "pole divisor" route (RR2.b of
`Submission/Work/NOTES_LEAD_jacobian_RR.md`) to Riemann's inequality and hence to the
finiteness of the genus.
-/
import Submission.Work.RiemannRoch.Adeles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The pole divisor of a rational function. -/
def poleDivisor (C : Curve k) (x : C.functionField) : C.Div := poleDiv C (diag C x)

@[simp]
theorem poleDivisor_apply (C : Curve k) (x : C.functionField) (Q : C.Place) :
    poleDivisor C x Q = max 0 (-(C.ordAt x Q)) := by
  rw [poleDivisor, poleDiv_apply, diag_apply]

theorem isEffective_poleDivisor (C : Curve k) (x : C.functionField) :
    (poleDivisor C x).IsEffective := by
  intro Q
  rw [poleDivisor_apply]
  exact le_max_left _ _

theorem div_add_poleDivisor_isEffective (C : Curve k) (x : C.functionField) :
    (C.div x + poleDivisor C x).IsEffective := by
  rw [C.isEffective_div_add_iff]
  intro Q
  rw [poleDivisor_apply]
  by_cases h : 0 ≤ C.ordAt x Q
  · have : max 0 (-(C.ordAt x Q)) = 0 := max_eq_left (by linarith)
    rw [this]; linarith
  · have : max 0 (-(C.ordAt x Q)) = -(C.ordAt x Q) := max_eq_right (by linarith)
    rw [this]; linarith

end

end Curve

end Work.RiemannRoch
