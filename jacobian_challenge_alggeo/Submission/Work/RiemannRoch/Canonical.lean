/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR: canonical divisors

A divisor `W` is *canonical* if it computes the index of speciality by duality:
`i D = l (W - D)` for every divisor `D` (Serre, *Algebraic Groups and Class Fields*, II §9;
the divisor of a nonzero Weil differential).  This is the form (RR5) in which
Riemann–Roch duality is exported to the rest of the Jacobian development: it is what makes
`{D : i D = 0}` an open / the charts of the group chunk explicitly computable, and it gives
the positive-dimensionality statements `l W = g`, `deg W = 2g - 2`.

The existence of a canonical divisor, and its basic properties, are in
`RiemannRoch/Duality.lean`.
-/
import Submission.Work.RiemannRoch.Differentials

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

/-- A divisor `W` is canonical if `i D = l (W - D)` for all divisors `D`. -/
def IsCanonical (C : Curve k) (W : C.Div) : Prop := ∀ D : C.Div, i C D = C.l (W - D)

theorem isCanonical_iff' {C : Curve k} {W : C.Div} :
    IsCanonical C W ↔ ∀ D : C.Div, i C D = C.l (W - D) := Iff.rfl

end

end Curve

end Work.RiemannRoch
