import Mathlib

/-! # The polynomial `GAB` of the C17 area (x-side, seven functions)

The leading coefficient of the order-two operator `M` of the CDT paper's equation (ODE) is the
septic

  `P2x = (X − 1)·X·(X + 1)·Q4x`,   `Q4x = 1 − 4abX + (4a²+4b²−2)X² − 4abX³ + X⁴`

(see `Work.C17.seventeen_indep`).  Over `ℂ` the quartic factors as
`(X² − cX + 1)·(X² − dX + 1)` with `c = ledC a b`, `d = ledD a b` (see
`Work.C17.led_factor`, `Work.C17.led_real_data`), so `P2x` becomes the septic

  `GAB c d = (X − 1)·X·(X + 1)·(X² − cX + 1)·(X² − dX + 1)`.

This file only *defines* this polynomial, so that the lemmas about it (its evaluations, and the
fact that its roots are simple) can be stated and proved in parallel.  It deliberately has no
dependency on the analytic part of the workspace.

The roots of `GAB c d` are `0, 1, −1` and the four roots of the two quadratics; for `2 < c`,
`2 < d`, `c ≠ d` they are pairwise distinct: that is the content of
`Work.C17.quartic_family_no_double_root`.
-/

namespace Work.C17

open Polynomial

noncomputable section

/-- `(X − 1)·X·(X + 1)·(X² − cX + 1)·(X² − dX + 1)` over `ℂ`: the leading coefficient `P2x`
of the operator `M`, after the factorisation of the quartic `Q4x` (see `Work.C17.led_factor`). -/
def GAB (c d : ℂ) : Polynomial ℂ :=
  (X - 1) * X * (X + 1) * ((X ^ 2 - C c * X + 1) * (X ^ 2 - C d * X + 1))

@[simp] lemma GAB_def (c d : ℂ) :
    GAB c d = (X - 1) * X * (X + 1) * ((X ^ 2 - C c * X + 1) * (X ^ 2 - C d * X + 1)) := rfl

end

end Work.C17
