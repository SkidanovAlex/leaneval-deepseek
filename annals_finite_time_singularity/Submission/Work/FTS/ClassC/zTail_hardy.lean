import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.TailDefs
import Submission.Work.FTS.H2.HQ.HardyZQ
import Submission.Work.FTS.H2.T2Qaux.SupAux
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.ClassC

theorem zTail_hardy {g : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen g)
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => g z θ) Filter.atTop (nhds 0))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hfin : Work.FTS.ClassC.zTail g θ ≠ ⊤) :
    ∀ z ∈ Set.Ioi (0 : ℝ), (g z θ) ^ 2 ≤ Work.FTS.ClassC.zTailR g θ := by
  intro z hz
  -- `θ` is an interior angle, so it lies in `Iθ`
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- the `z`-slice is `C¹` on `(0,∞)`, since `g` is `C^∞` on the open quadrant
  have hcd : ContDiffOn ℝ 1 (fun s : ℝ => g s θ) (Set.Ioi (0 : ℝ)) :=
    (hso.curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
  have hdec' : Filter.Tendsto (fun s : ℝ => g s θ) Filter.atTop (nhds 0) := hdec θ hθI
  -- the radial Hardy inequality in `lintegral` form
  have hkey := Work.FTS.H2.T2Qaux.hardyZQ_lintegral hcd hdec' hz
  -- `zTail g θ` is the lintegral of exactly that integrand
  have hzTail : Work.FTS.ClassC.zTail g θ =
      MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz)
        (fun s : ℝ =>
          ENNReal.ofReal ((s * deriv (fun s' => g s' θ) s) ^ 2 * (Work.Spaces.w s) ^ 2)) := by
    rw [Work.FTS.ClassC.zTail_eq_lintegral]
    apply MeasureTheory.lintegral_congr
    intro s
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
  calc (g z θ) ^ 2
      = ENNReal.toReal (ENNReal.ofReal ((g z θ) ^ 2)) :=
        (ENNReal.toReal_ofReal (sq_nonneg _)).symm
    _ ≤ ENNReal.toReal (Work.FTS.ClassC.zTail g θ) :=
        ENNReal.toReal_mono hfin (by rw [hzTail]; exact hkey)
    _ = Work.FTS.ClassC.zTailR g θ := rfl

end Work.FTS.ClassC
