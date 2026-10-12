import ChallengeDeps
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.CloseFS` — the two close conditions

`closeThresholdFS v μ = μK_ℓ⁻²/(2¹⁴π)` (the `F9` correction of the design) is *smaller*
than the corpus's `Work.BoseFixR.closeThreshold v μ = μK_ℓ⁻²`, so the chapter's close region
`CloseCondFS` is *inside* the corpus's `CloseCond`.  This module records the two
comparisons, so that a consumer can move between the chapter's statements (which live at
`CloseCondFS`) and the corpus's `BogOpBound`-style statements (which live at `CloseCond`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The corrected threshold is at most the corpus's: the correction is the factor
`1/(2¹⁴π) ≤ 1`. -/
theorem closeThresholdFS_le (v : ℝ³ → ℝ) (μ : ℝ) (hav : 0 < a v) (hμ : 0 < μ) :
    closeThresholdFS v μ ≤ closeThreshold v μ := by
  have ht : 0 < μ * a v ^ 3 := by positivity
  have hKl : 0 ≤ (paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) := by
    have hpos : 0 < (paramsAt μ (a v)).Kl := by
      have h1 : (paramsAt μ (a v)).Kl = Work.BoseBox.fsXp (μ * a v ^ 3) (-(3 / 2 : ℝ)) := rfl
      rw [h1]
      exact Work.BoseBox.fsXp_pos ht
    exact Real.rpow_nonneg hpos.le _
  have hπ : (1 : ℝ) / ((2 : ℝ) ^ 14 * π) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hfac : 0 ≤ μ * (paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) :=
    mul_nonneg hμ.le hKl
  rw [closeThresholdFS, closeThreshold]
  calc μ * (paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π)
      = (μ * (paramsAt μ (a v)).Kl ^ (-(2 : ℝ))) * (1 / ((2 : ℝ) ^ 14 * π)) := by ring
    _ ≤ (μ * (paramsAt μ (a v)).Kl ^ (-(2 : ℝ))) * 1 :=
        mul_le_mul_of_nonneg_left hπ hfac
    _ = μ * (paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) := by ring

/-- The chapter's close region is inside the corpus's. -/
theorem CloseCondFS.toCloseCond {v : ℝ³ → ℝ} {μ ρ : ℝ} (hav : 0 < a v) (hμ : 0 < μ)
    (h : CloseCondFS v μ ρ) : CloseCond v μ ρ :=
  le_trans h (closeThresholdFS_le v μ hav hμ)

end Work.BoseBogFS
