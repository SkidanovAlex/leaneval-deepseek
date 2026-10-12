import Mathlib.Analysis.Real.Sqrt
import Submission.Work.BoseBogFS.ReserveArith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.WindowArith` — the reserve window in linear form

`reserveLoss_sigmaChoice_le` (in `ReserveArith.lean`) discharges the reserve slot `hResB`
from the single window condition `2√(G·(Kbar+S)) + G ≤ B`.  This module turns that window
condition into **two linear conditions**, which is the form in which the honest data
supplies it:

* `G ≤ B/2` — `G` is the (super-polynomially small) `Σ_{RHi}𝒟_kγ_k²`,
* `G·(winKbar E Dsup + zpKapSum E ρ) ≤ B²/16` — the product of the small `G` with the
  polynomially large `Kbar + S`.

Both are immediate from a bound `G ≤ (small power of X)` together with the polynomial
bounds on `winKbar`/`zpKapSum` (`qw_KzBogFS_le_window`, `qp_KzBogFS_le_window`) and the
χ̂-decay of `Work.BoseK15` — that part is the GATE/ESTIMATES node's data; the arithmetic
below is what the chapter itself owes.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- **The window from two linear conditions.** -/
theorem two_sqrt_mul_add_le {B G S : ℝ} (hB : 0 ≤ B) (hG0 : 0 ≤ G) (hS0 : 0 ≤ S)
    (hG : G ≤ B / 2) (hGS : G * S ≤ B ^ 2 / 16) :
    2 * Real.sqrt (G * S) + G ≤ B := by
  have h2 : Real.sqrt (G * S) ≤ B / 4 := by
    calc Real.sqrt (G * S) ≤ Real.sqrt ((B / 4) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = B / 4 := Real.sqrt_sq (by linarith)
  linarith

/-- **The reserve slot in linear form.**  Assuming the two linear conditions `G ≤ B/2` and
`G(Kbar+S) ≤ B²/16` (with `B = C₅·errBracket v R μ`, `Kbar = winKbar E Dsup`,
`S = zpKapSum E ρ`), the reserve cost is `≤ B` at an explicit `σ > 0` (`sigmaChoice` when
`G > 0`, `B/(2(Kbar+S))` when `G = 0`). -/
theorem exists_sigma_reserveLoss_le (E : Q3Env Mode) (ρ Dsup G B : ℝ)
    (hG0 : 0 ≤ G) (hS : 0 < winKbar E Dsup + zpKapSum E ρ) (hBe : 0 < B)
    (hG : G ≤ B / 2) (hGS : G * (winKbar E Dsup + zpKapSum E ρ) ≤ B ^ 2 / 16) :
    ∃ σ : ℝ, 0 < σ ∧ reserveLoss E ρ Dsup G σ ≤ B := by
  have hS0 : 0 ≤ winKbar E Dsup + zpKapSum E ρ := hS.le
  have hwin : 2 * Real.sqrt (G * (winKbar E Dsup + zpKapSum E ρ)) + G ≤ B :=
    two_sqrt_mul_add_le hBe.le hG0 hS0 hG hGS
  by_cases hGz : G = 0
  · refine ⟨B / (2 * (winKbar E Dsup + zpKapSum E ρ)), by positivity, ?_⟩
    rw [reserveLoss, hGz]
    have h2 : B / (2 * (winKbar E Dsup + zpKapSum E ρ)) * winKbar E Dsup
        + B / (2 * (winKbar E Dsup + zpKapSum E ρ)) * zpKapSum E ρ = B / 2 := by
      field_simp
    rw [h2]
    ring_nf
    linarith
  · refine ⟨sigmaChoice E ρ Dsup G, ?_, reserveLoss_sigmaChoice_le E ρ Dsup G B hG0 hS hwin⟩
    rw [sigmaChoice]
    exact Real.sqrt_pos.mpr (div_pos (lt_of_le_of_ne hG0 (Ne.symm hGz)) hS)

end Work.BoseBogFS
