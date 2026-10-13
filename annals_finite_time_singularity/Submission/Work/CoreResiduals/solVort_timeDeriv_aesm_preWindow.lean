import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.Defs
import Submission.Work.ConstructionInstance.solVort_integrable
import Submission.Work.ConstructionInstance.hasDerivAt_selfSimVort_slice
import Submission.Work.StabilityFar.Decay.aestronglyMeasurable_timeDeriv_slice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- **The time-derivative slice of the constructed vorticity is almost everywhere strongly
measurable on the half-window `preWindow T = Ioo (-2) T`.**

This is the local form of `Work.StabilityFar.Decay.aestronglyMeasurable_timeDeriv_slice`: at each
`t` of the *open* window `Ioo (-2) T` the two-sided window `(t-ε, t+ε)` can be chosen inside the
window, where

* every slice `solVort P · s` is integrable (`solVort_integrable`), hence almost everywhere
  strongly measurable, and
* `s ↦ solVort P y s` is differentiable with derivative `timeDeriv (solVort P) y s`
  (`hasDerivAt_selfSimVort_slice`). -/
theorem solVort_timeDeriv_aesm_preWindow {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      MeasureTheory.AEStronglyMeasurable
        (fun y : Work.CoreResiduals.R3 => FiniteTimeSingularity.timeDeriv
          (Work.ConstructionInstance.solVort P) y t) MeasureTheory.volume := by
  intro t ht
  obtain ⟨ht1, ht2⟩ := ht
  have hpos1 : 0 < t + 2 := by linarith
  have hpos2 : 0 < P.T - t := by linarith
  set ε : ℝ := min (t + 2) (P.T - t) / 2 with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact half_pos (lt_min hpos1 hpos2)
  have hεle1 : ε ≤ (t + 2) / 2 := by
    rw [hεdef]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hεle2 : ε ≤ (P.T - t) / 2 := by
    rw [hεdef]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  -- the two-sided window lies inside the half-window `preWindow T`
  have hwin : ∀ s ∈ Set.Ioo (t - ε) (t + ε), s ∈ Work.ConstructionInstance.preWindow P.T := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    refine ⟨by linarith, by linarith⟩
  refine Work.StabilityFar.Decay.aestronglyMeasurable_timeDeriv_slice hεpos ?_ ?_
  · intro s hs y
    have hd := Work.ConstructionInstance.hasDerivAt_selfSimVort_slice
      (p := Work.ConstructionInstance.profExp α) (g := P.g) (L := P.L) (lam := P.lam)
      (T := P.T) P.hgdiff P.hlam P.hlamdif (hwin s hs) y
    simpa only [Work.ConstructionInstance.solVort] using hd
  · intro s hs
    exact (Work.ConstructionInstance.solVort_integrable P s (hwin s hs)).aestronglyMeasurable

end Work.CoreResiduals
