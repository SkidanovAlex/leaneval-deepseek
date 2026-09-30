/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR: numerical invariants of a canonical divisor

For a canonical divisor `W` (i.e. `i D = l (W - D)` for all `D`):

* `IsCanonical.l_eq` — `l W = g` (the space of sections of the canonical class has dimension `g`);
* `IsCanonical.deg` — `deg W = 2g - 2`.

Both are immediate from Riemann–Roch and `l 0 = 1`.
-/
import Submission.Work.RiemannRoch.Canonical
import Submission.Work.RiemannRoch.RRLib
import Submission.Work.RiemannRoch.Genus

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- A canonical divisor has `l W = g`: it is the divisor of a nonzero Weil differential, whose
sections form the dual of `H^1(C, O_C)` in degree zero. -/
theorem IsCanonical.l_eq {C : Curve k} {W : C.Div} (hW : IsCanonical C W) :
    C.l W = genus C := by
  have h := hW 0
  rw [sub_zero] at h
  exact h.symm

/-- A canonical divisor has degree `2g - 2`. -/
theorem IsCanonical.deg {C : Curve k} {W : C.Div} (hW : IsCanonical C W) :
    C.deg W = 2 * (genus C : ℤ) - 2 := by
  have hRR := riemannRoch C W
  have hiW : i C W = 1 := by
    have h := hW W
    rw [sub_self] at h
    rw [h, l_zero]
  have hlW : C.l W = genus C := hW.l_eq
  rw [hiW, hlW] at hRR
  have : (genus C : ℤ) - 1 = C.deg W + 1 - (genus C : ℤ) := by exact_mod_cast hRR
  linarith

end

end Curve

end Work.RiemannRoch
