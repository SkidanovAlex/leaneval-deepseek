/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinTwData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The two forms of the twisted Klein quadrics agree

The twisted Klein quadrics occur in two shapes in this workspace:

* `Work.MotV.kleinTw a b h y k` (`Submission/Work/MotV/Defs.lean`) is the *definitional* one, built
  from the monomials `twMon h y i l = (if 5 ≤ i + l then h else 1) · y_i · y_l`; it is the form in
  which the substitution identity `Work.MotV.kleinTw_subst`
  (`kleinP a b (w^i y_i) = w^{4k} · kleinTw a b (w^5) y`) is stated, and hence the form in which
  `Work.MotK.TGen.TwCoordGKleinTw` (the twisted Klein equations for the generic T-twist) is proved.
* `Work.MotK.kleinTwP a b h y : Fin 5 → R` (`Submission/Work/MotK/KleinTwData.lean`) is the
  *explicit* expansion `![kleinTwP0, …, kleinTwP4]` used by the twisted link data
  (`kleinTwStereo`, `kleinTwRulePt`, `KleinTwLinkComp1`, …).

This file proves that the two agree componentwise, so that the twisted Klein equations can be used
in either vocabulary (e.g. to evaluate an ideal-membership in the `kleinTwP`-generated ideal of the
twisted Klein curve at the twisted coordinates).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- **The twisted Klein quadrics agree**: `Work.MotV.kleinTw` (the `twMon`-form) coincides with
`Work.MotK.kleinTwP` (the explicit Pfaffian expansion). -/
theorem kleinTw_eq_kleinTwP (a b h : R) (y : Fin 5 → R) (k : Fin 5) :
    Work.MotV.kleinTw a b h y k = kleinTwP a b h y k := by
  fin_cases k <;>
    simp only [Work.MotV.kleinTw, Work.MotV.twMon, kleinTwP, kleinTwP0, kleinTwP1, kleinTwP2,
      kleinTwP3, kleinTwP4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] <;>
    norm_num <;>
    first | refl_ring1 | ring

/-- Componentwise form of `kleinTw_eq_kleinTwP`. -/
theorem kleinTw_eq_kleinTwP' (a b h : R) (y : Fin 5 → R) :
    Work.MotV.kleinTw a b h y = kleinTwP a b h y :=
  funext fun k => kleinTw_eq_kleinTwP a b h y k

theorem kleinTwP_eq_kleinTw (a b h : R) (y : Fin 5 → R) (k : Fin 5) :
    kleinTwP a b h y k = Work.MotV.kleinTw a b h y k :=
  (kleinTw_eq_kleinTwP a b h y k).symm

end Work.MotK.TGen
