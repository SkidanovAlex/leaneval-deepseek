import ChallengeDeps
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.CloseCondFSCompat` — the `CloseCond` / `CloseCondFS` interface bridges

The area's interface change `F9` replaced FS `eq:Close`'s threshold `closeThreshold` by the
smaller `closeThresholdFS = closeThreshold/(2¹⁴π)` (the *corrected* threshold: the gap
absorption `|ρ−μ|·16πa·16·N ≤ (b/4ℓ²)N` needs the universal constant).  Two consumers were
written against the *other* of the two definitions and now fail to typecheck:

* `Submission/Work/BoseGateFS/GateHonest.lean` (`hρ : CloseCondFS v μ ρ` fed to a lemma that
  wants `CloseCond v μ ρ`) — needs `closeCond_of_closeCondFS` below;
* `Submission/Work/BoseFixR/RB5FSFixAux.lean` (`hclose : CloseCond v μ μ` fed to the gate at
  `ρ = μ`, which wants `CloseCondFS v μ μ`) — needs `closeCondFS_self` below (the *other*
  implication is false: the FS threshold is *smaller*).

Both are one-line applications; they are collected here (rather than by editing the two
modules by hand) so that their owners can point at them.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `closeThresholdFS` is `closeThreshold/(2¹⁴π)`, i.e. the corrected threshold is the
*smaller* one (the two differ exactly by the universal factor `2¹⁴π`). -/
lemma closeThresholdFS_eq (v : ℝ³ → ℝ) (μ : ℝ) :
    closeThresholdFS v μ = Work.BoseFixR.closeThreshold v μ / ((2 : ℝ) ^ 14 * Real.pi) := by
  simp only [closeThresholdFS, Work.BoseFixR.closeThreshold]

/-- The corrected threshold is nonnegative in the dilute regime. -/
lemma closeThresholdFS_nonneg {v : ℝ³ → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    0 ≤ closeThresholdFS v μ := by
  have hd : 0 < Work.BoseFixR.dil v μ := by rw [Work.BoseFixR.dil]; positivity
  have hKl : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl := by
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos hd
  rw [closeThresholdFS_eq]
  exact div_nonneg (mul_nonneg hμ.le (Real.rpow_nonneg hKl.le _)) (by positivity)

/-- **`CloseCond` at `ρ = μ` in the corrected vocabulary**: the gate at the density `μ`
itself (this is the form `Work.BoseFixR.RB5FSFixAux` feeds to `RViewFS`'s gate conjunct). -/
theorem closeCondFS_self {v : ℝ³ → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    CloseCondFS v μ μ := by
  rw [CloseCondFS, sub_self, abs_zero]
  exact closeThresholdFS_nonneg hμ hav

/-- **The corrected threshold implies the old one**: `CloseCondFS v μ ρ → CloseCond v μ ρ`
(the `2¹⁴π ≥ 1` factor, `F9`'s note in `README.md` §4; the converse is false). -/
theorem closeCond_of_closeCondFS {v : ℝ³ → ℝ} {μ ρ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
    (h : CloseCondFS v μ ρ) : Work.BoseFixR.CloseCond v μ ρ := by
  have hd : 0 < Work.BoseFixR.dil v μ := by rw [Work.BoseFixR.dil]; positivity
  have hKl : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl := by
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos hd
  have hthr : 0 ≤ Work.BoseFixR.closeThreshold v μ :=
    mul_nonneg hμ.le (Real.rpow_nonneg hKl.le _)
  have hfac : (1 : ℝ) / ((2 : ℝ) ^ 14 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  unfold Work.BoseFixR.CloseCond
  unfold CloseCondFS at h
  calc |ρ - μ| ≤ closeThresholdFS v μ := h
    _ = Work.BoseFixR.closeThreshold v μ / ((2 : ℝ) ^ 14 * Real.pi) := closeThresholdFS_eq v μ
    _ ≤ Work.BoseFixR.closeThreshold v μ * 1 := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa using hfac) hthr
    _ = Work.BoseFixR.closeThreshold v μ := by ring

end Work.BoseBoxFock
