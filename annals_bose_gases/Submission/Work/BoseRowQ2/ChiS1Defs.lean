import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseRowQ2.chiHat_abs_tail_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.ChiS1Defs` — the first lattice moment `S₁` of the corpus `χ̂`

`S₁ = Σ_{m ∈ ℤ³} ‖2πm‖·|χ̂(2πm)|` (`Work.BoseB4.vec m = 2πm`), the constant that controls the
lattice commutator `[χ, f_L(D)]` in the lead's NH ruling (2026-10-08, `LEAD_RULING_NH.md`):

`‖[χ, f_L(D)]‖ ≤ C_fc·S₁/κ_lat`,   `κ_lat = ℓκ = honCutRad v μ`.

It is finite by `chiHat_abs_tail_le` (lattice tail `≲ R^{-101}`) — that is statement **(A1)**
`Work.BoseRowQ2.chiS1_summable`, delegated.

This definition and the two lemmas that follow are the *first two steps* of the lead's work list for
this area (row 3 at the frozen `NH` via the commutator route: `GchiAtN` + `ArithAt2`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowQ2

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB

/-- The first absolute moment of the lattice `χ̂`: `S₁ = Σ_{m∈ℤ³} ‖2πm‖·|χ̂(2πm)|`
(≈ 254.4 for the smoothTransition model χ; finite by `chiHat_abs_tail_le`). -/
def chiS1 : ℝ := ∑' m : Fin 3 → ℤ, ‖Work.BoseB4.vec m‖ * |chiHat (Work.BoseB4.vec m)|

end Work.BoseRowQ2
