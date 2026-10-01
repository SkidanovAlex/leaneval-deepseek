/-
# LinnikContract2 — `area7`: AREA 7 re-proved (unconditional, **round 2 final**)

Against the round-2 contract, `Area7` is now `A7/WindowAssembly.lean`'s `area7_window`
(**proved**, sorry-free, no axioms beyond the three permitted ones).  That assembly handles the
three cases at every modulus:

* **Case A** (`IsZ χ₁ ρ₁`): the wide minimiser is a working-region zero, so round 1's `§14`/`§15`
  machinery (`Work.A7.sec14_uniform`, `Work.A7.sec15_uniform`) applies after
  `IsMin1.toRound1`.
* **Case B.1** (`¬ IsZ χ₁ ρ₁`, `29/50 ≤ λ₁`): the two-pivot `§15` argument `A7/sec15_caseB`.
* **Case B.2, the window** (`¬ IsZ χ₁ ρ₁`, `348/1000 ≤ λ₁ < 29/50`): `(Z1)` gives the lower bound
  on `λ₁`, the §15 argument is run at the *narrow* minimiser (`A7/window_step` +
  `A7/WindowAPI`) with the five numerical certificates `A7/WindowCert.lean` (`win_g1`–`win_g5`),
  and the branch `λ̃ > Λ` is covered by the plain tail bound.

The numbered zero itself is supplied by the proved `Area0` (`WideMinExists`); no setting clause is
carried (`NumZeroNarrow` has been deleted from the contract).
-/
import Mathlib
import Submission.Work.LinnikContract2.Areas
import Submission.Work.LinnikContract2.A7.WindowAssembly

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikContract2

/-- **AREA 7, re-proved (unconditional at the round-2 contract).** -/
theorem area7 : Area7 := A7.area7_window

end Work.LinnikContract2
