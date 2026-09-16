/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.GenFun

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial
open scoped BigOperators

/-!
# Regression checks for the generating function

The generating function identity `A_genfun` was validated coefficientwise in exact `F_q[T]`
arithmetic for `q ∈ {2,3,4,5,7,9}` (degrees `≤ 12`, script `/tmp/ses299/gf.py`), using Carlitz's
formula for `A_n` — independently of the Lean proof.
-/

namespace GenFunRegression

attribute [local instance 100] Classical.decEq

open ZagierHoffmanPositiveChar

/-- Carlitz's generating function over `F₂`. -/
example : PowerSeries.mk (fun n => A (ZMod 2) n) *
    (1 + PowerSeries.X - PowerSeries.C ((carlitzOne (ZMod 2)) ^ (Nat.card (ZMod 2) - 1)) *
      PowerSeries.X ^ Nat.card (ZMod 2)) = -PowerSeries.X :=
  A_genfun (ZMod 2)

/-- The specialisation generating function over `F₃`. -/
example : PowerSeries.mk (fun n => bspec (ZMod 3) n) *
    (1 - PowerSeries.X + PowerSeries.C ((carlitzOne (ZMod 3)) ^ (Nat.card (ZMod 3) - 1)) *
      PowerSeries.X ^ Nat.card (ZMod 3)) = 1 :=
  bspec_genfun (ZMod 3)

/-- Coefficient extraction from the generating function: the constant term is `b_0 = 1`. -/
example : PowerSeries.coeff 0 (PowerSeries.mk (fun n => bspec (ZMod 2) n)) = 1 := by
  rw [PowerSeries.coeff_mk]
  exact bspec_zero (ZMod 2)

/-- `A_0 = 0` (the empty power sum) over `F₂`. -/
example : A (ZMod 2) 0 = 0 := A_zero (ZMod 2)

end GenFunRegression
