import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Reduce
import Submission.Work.BoseFixB3.Split.lowSlotBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.leakFn_abs_le`

The leakage function `leakFn fc κ ℓ y = 1 − lowMult fc κ ℓ (fun _ => 1) y`
(`Submission/Work/BoseFixB3/CS/Reduce.lean`) is **bounded uniformly in `y`**:

`|leakFn fc κ ℓ y| ≤ 1 + (2π)⁻³ ℓ³ · vol(B(0, 2κ))`.

The proof is the `Split.lowMult_abs_le` estimate (`Submission/Work/BoseFixB3/Split/lowSlotBound.lean`)
at the constant function `ψ ≡ 1`: the multiplier symbol is supported on `‖p‖ ≤ 2κ` and bounded by
`1`, while `‖kinFT(1_{acube ℓ}) p‖ ≤ ℓ³` (`Split.integral_indicator_norm_le`).  This is the
`hB` hypothesis of `CS.Pieces.leakCoupl_swap`/`leakCoupl_abs_le`.
-/

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory

/-- `|1 − x| ≤ 1 + |x|`. -/
lemma abs_one_sub_le (x : ℝ) : |1 - x| ≤ 1 + |x| := by
  simpa using abs_sub_le (1 : ℝ) 0 x

theorem leakFn_abs_le (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    (y : EuclideanSpace ℝ (Fin 3)) :
    |Work.BoseFixB3.CS.leakFn fc κ ℓ y|
      ≤ 1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          (MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * κ))).toReal := by
  -- the constant function `1` is bounded by `1` on the box
  have hψ : ∀ z ∈ Submission.BoseGases.acube ℓ, |Work.BoseFixB3.CS.oneFn z| ≤ (1 : ℝ) := by
    intro z _
    simp [Work.BoseFixB3.CS.oneFn]
  -- its box-localised fibre has `L¹`-mass at most `ℓ³`
  have hD1 := Work.BoseFixB3.Split.integral_indicator_norm_le (ℓ := ℓ) (M := (1 : ℝ))
    hℓ zero_le_one (ψ := Work.BoseFixB3.CS.oneFn) hψ
  have hD : ∫ z, ‖(((Submission.BoseGases.acube ℓ).indicator (Work.BoseFixB3.CS.oneFn) z : ℝ) : ℂ)‖
      ≤ ℓ ^ 3 := by
    simpa using hD1
  -- the multiplier estimate at `D = ℓ³`
  have hlow := Work.BoseFixB3.Split.lowMult_abs_le (fc := fc) (κ := κ) (ℓ := ℓ) (D := ℓ ^ 3)
    hκ (by positivity) hD y
  rw [show Work.BoseFixB3.CS.leakFn fc κ ℓ y
      = 1 - Work.BoseBoxFix.lowMult fc κ ℓ Work.BoseFixB3.CS.oneFn y from rfl]
  calc |1 - Work.BoseBoxFix.lowMult fc κ ℓ Work.BoseFixB3.CS.oneFn y|
      ≤ 1 + |Work.BoseBoxFix.lowMult fc κ ℓ Work.BoseFixB3.CS.oneFn y| :=
        abs_one_sub_le _
    _ ≤ 1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          (MeasureTheory.volume
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * κ))).toReal := by
        linarith [hlow]

end Work.BoseFixB3.CS.Pieces
