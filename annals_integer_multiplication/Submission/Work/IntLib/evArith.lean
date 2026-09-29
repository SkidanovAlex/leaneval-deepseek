import Mathlib
import Submission.Work.IntLib.evDefs

/-!
# `IntLib` / `evalPoly`: the cost budget

The time budget of the assembled `evalPoly` word is

`polyBudget hs b = Σ_{h ∈ hs} isz h + hs.length * (b + 1) + isz b + 1`

and the constant chosen for the whole word is `polyK` (each phase's coefficient is absorbed by the
factor `1000`).  The pure arithmetic facts (each phase's cost fits into the budget, and the three
phase coefficients fit into `polyK`) are proved in `evArithNe` (`hs ≠ []`) and `evArithNil`
(`hs = []`).
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-- The time budget of the `evalPoly` word for a chain `hs` of digits at base `2^b`. -/
def polyBudget (hs : List ℕ) (b : ℕ) : ℕ :=
  (hs.map fun h => HvdH.isz (h : ℤ)).sum + hs.length * (b + 1) + HvdH.isz (b : ℤ) + 1

/-- The constant of the assembled `evalPoly` word. -/
def polyK (KP KCM KR KEP KE KC KA KZ : ℕ) : ℕ :=
  1000 * (KP * (KCM + KR + 1) + KEP * (KE + 40) + (KR + KC + KA + KZ + 20) + 1)

/-- The budget is positive. -/
theorem polyBudget_pos (hs : List ℕ) (b : ℕ) : 1 ≤ polyBudget hs b := by
  rw [polyBudget]; omega

/-- `isz` of a natural number. -/
theorem isz_nat (b : ℕ) : HvdH.isz (b : ℤ) = b.size + 2 := by simp [HvdH.isz]

end Work.IntLib
