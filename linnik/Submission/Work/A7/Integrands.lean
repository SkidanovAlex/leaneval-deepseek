/-
# Area 7 — integrands of `boxSum` / `boxAbs`

`Work.LinnikContract.boxSum` and `Work.LinnikContract.boxAbs` are `finsum`s of the
indicator functions `cfun` and `bfun` introduced here.  Factoring the integrands out
lets the (finite-support) estimates be stated without any `if`-expression, so they can
be delegated and proved independently of `Classical` decidability plumbing.
-/
import Mathlib
import Submission.Work.LinnikAreas.A7.Defs

open scoped Classical BigOperators
open DirichletCharacter Complex

namespace Work.A7

open Work.LinnikContract

/-- The complex integrand of `boxSum q L K R χ` (zero outside `InBox q R`). -/
noncomputable def cfun (q : ℕ) [NeZero q] (L K R : ℝ) (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  fun ρ => if InBox q R ρ then (zeroMult χ ρ : ℂ) * Hk L K ((1 - ρ) * Real.log q) else 0

/-- The real integrand of `boxAbs q K R χ` (zero outside `InBox q R`). -/
noncomputable def bfun (q : ℕ) [NeZero q] (K R : ℝ) (χ : DirichletCharacter ℂ q) : ℂ → ℝ :=
  fun ρ => if InBox q R ρ then (zeroMult χ ρ : ℝ) * ‖F2 K ((1 - ρ) * Real.log q)‖ else 0

end Work.A7
