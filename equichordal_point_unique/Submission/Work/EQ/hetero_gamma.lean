import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.hetero_local
import Submission.Work.EQ.hetero_box
import Submission.Work.EQ.arcInv_eqU
import Submission.Work.EQ.polarPt_basic

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## The explicit inverse of `eqU` on the arc

Given a stable germ `h` whose curve lies on the equichordal curve near `A₁` (`germPt_mem_arc`,
in `hetero_box.lean`), the heteroclinic connection is obtained by pulling the germ curve back
along the inverse of `eqU` on the upper arc.  The explicit formula for that inverse is `arcInv`
below: for `z = O₁ + s e^{iψ}` (`s = ‖z - O₁‖ < 1`) the preimage of `z` under `eqU` is
`O₂ + (1 - s) e^{iψ}`; the formula is stated without angles as
`O₂ + (1 - ‖w‖) * w/‖w‖` with `w = z + O₂ = z - O₁`.

`arcInv_eqU` (a companion file) verifies that `arcInv` really inverts `eqU` on the upper half
plane; `eqU_arcInv` below is the converse identity `eqU a (arcInv a z) = z`. -/

namespace Work.EQ

open Complex Filter
open scoped Topology

noncomputable section

variable {a : ℝ}

/-- The explicit inverse of `eqU`: the point `O₂ + (1 - s) * w/‖w‖` where `w = z - O₁` and
`s = ‖w‖`. -/
def arcInv (a : ℝ) (z : ℂ) : ℂ :=
  (((a / 2 : ℝ)) : ℂ) +
    (1 - ‖z + (((a / 2 : ℝ)) : ℂ)‖) *
      ((z + (((a / 2 : ℝ)) : ℂ)) / ‖z + (((a / 2 : ℝ)) : ℂ)‖)

/-- The `n`-fold iterate of `arcInv`. -/
def arcInvN (a : ℝ) (n : ℕ) (z : ℂ) : ℂ := (arcInv a)^[n] z

theorem norm_ofReal_eq (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, show r * r = r ^ 2 by ring, Real.sqrt_sq_eq_abs]

/-- `arcInv` inverts `eqU` on the open upper half plane (companion file). -/
theorem arcInv_eqU' {P : ℂ} (him : 0 < (P - (((a / 2 : ℝ)) : ℂ)).im)
    (hr : ‖P - (((a / 2 : ℝ)) : ℂ)‖ < 1) : arcInv a (eqU a P) = P :=
  arcInv_eqU him hr

end

end Work.EQ
