import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty

/-- The clamped mode coefficient is a.e. measurable: it agrees with `cmode m F` on the open
half-line `(0,∞)`, where the latter is a.e. strongly measurable
(`Work.EllipticEst.ModalSolution.aesm_cmode`), and it vanishes off `(0,∞)`.

Formally, the clamp is the indicator of `(0,∞)` applied to `cmode m F`, and
`aemeasurable_indicator_iff` converts a.e. measurability of an indicator into a.e. measurability
of the function for the restricted measure on the set. -/
theorem aemeasurable_cmode_clamp {α : ℝ} {F : ℝ → ℝ → ℝ} (m : ℕ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) :
    AEMeasurable (fun z : ℝ => if 0 < z then Work.FTS.PhiStar.Series.cmode m F z else 0) := by
  have haesm : AEStronglyMeasurable (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Work.EllipticEst.ModalSolution.aesm_cmode hsm m
  have hc : AEMeasurable (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    aestronglyMeasurable_iff_aemeasurable.mp haesm
  have hkey : AEMeasurable (Set.indicator (Set.Ioi (0 : ℝ))
      (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z)) (volume : Measure ℝ) :=
    (aemeasurable_indicator_iff measurableSet_Ioi).mpr hc
  have hpt : ∀ z : ℝ, Set.indicator (Set.Ioi (0 : ℝ))
      (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z) z
        = (fun z : ℝ => if 0 < z then Work.FTS.PhiStar.Series.cmode m F z else 0) z := by
    intro z
    by_cases hz : 0 < z
    · simp [Set.indicator_of_mem, Set.mem_Ioi, hz]
    · simp [Set.indicator_of_notMem, Set.mem_Ioi, hz]
  exact (aemeasurable_congr (μ := (volume : Measure ℝ))
    (Filter.Eventually.of_forall hpt)).mp hkey

end Work.FTS.PhiStar.Honesty
