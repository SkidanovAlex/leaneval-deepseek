import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.ClassCHon.Hcoef.near_cs
import Submission.Work.FTS.ClassCHon.Hcoef.far_cs
import Submission.Work.FTS.ClassCHon.Hcoef.near_inner
import Submission.Work.FTS.ClassCHon.Hcoef.far_inner
import Submission.Work.FTS.ClassCHon.Hcoef.radGreen_split_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.HcoefSplit

theorem radGreen_split_le_gen {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {m : ℕ} (hm : 1 ≤ m)
    {c : ℝ → ℝ} {z L B : ℝ} (hz : 0 < z) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hcL : ∀ t ∈ Set.Icc (z / 2) (2 * z), |c t| ≤ L)
    (hc : MeasureTheory.IntegrableOn (fun t : ℝ => (c t * Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t * Work.Spaces.w t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hBs : Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * Work.Spaces.w t) ^ 2) ≤ B) :
    |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ Work.FTS.EllExist.rgK α m *
      (L * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)
        + B * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
              / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
            + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
              / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3))) := by
  -- the two exponent hypotheses of `radGreen_split_le` are implied by `0 < α ≤ 1/4`, `1 ≤ m`
  have hq : 1 < Work.FTS.EllExist.rgQ α m := by
    have h := Work.FTS.EllExist.rgQ_ge hα hα4 hm
    linarith
  have hp : 3 / 2 < Work.FTS.EllExist.rgP α m := by
    have h := Work.FTS.EllExist.rgP_ge hα hα4 hm
    linarith
  exact Work.FTS.ClassCHon.Hcoef.radGreen_split_le hα hz hL hB hq hp hcL hc hcm hBs

end Work.FTS.ClassCHon.HcoefSplit
