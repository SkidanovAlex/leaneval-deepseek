import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Pot.aemeasurable_wPairC_prod
import Submission.Work.BoseFixB2.Pot.lintegral_wPairC_le
import Submission.Work.BoseFixR.PotLocDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixR.lintegral_wPairC_acube_le`

The **box-localised** `L¹`-bound for the χ-renormalised two-body kernel: for `0 < ℓ` and a
numerator `h` that is merely *integrable on the closed ball of radius `ℓ`* (in particular for
a locally integrable `h`, since that ball is compact),

    ∫⁻_{a ∈ acube ℓ} ∫⁻_{b} ‖wPairC ℓ h a b‖ₑ ≤ ofReal (ℓ³ · ∫_{‖z‖ ≤ ℓ} |h z|).

The global version with `Integrable h` is `Work.BoseFixB2.Pot.lintegral_wPairC_le`.  The point
here is that the `χ_ℓ`-factors confine the integration to the box: whenever both cutoffs are
nonzero we have `‖a‖ ≤ ℓ/2` and `‖b‖ ≤ ℓ/2`, hence `‖a − b‖ ≤ ℓ`, so `h` is only ever evaluated
on `closedBall 0 ℓ`.  Accordingly we truncate `h` to that ball (`hₙ = 1_{closedBall 0 ℓ} · h`),
note that `wPairC ℓ h = wPairC ℓ hₙ` *pointwise* (both sides vanish unless both cutoffs are
nonzero, and on that region the truncated numerator agrees with `h`), and apply the global
bound to the integrable `hₙ`.

This is the analytic core of `Work.BoseFixR.PotWordUIntegrableLoc`: with only *local*
integrability of `v` and `g`, it supplies the two finiteness estimates
(`∫⁻` of the pair kernel, resp. of `chemQ`) on which the integrability of the bare word
`potWordU N v g ℓ μ 0` over the box `abox N ℓ` rests.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem lintegral_wPairC_acube_le {ℓ : ℝ} (hℓ : 0 < ℓ)
    {h : E3 → ℝ}
    (hh : MeasureTheory.IntegrableOn h (Metric.closedBall 0 ℓ) MeasureTheory.volume) :
    (∫⁻ a : E3,
        (∫⁻ b : E3, ‖Submission.BoseGases.wPairC ℓ h a b‖ₑ)
        ∂(MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
      ≤ ENNReal.ofReal (ℓ ^ 3 * ∫ z in Metric.closedBall 0 ℓ, |h z|) := by
  set s : Set E3 := Metric.closedBall 0 ℓ with hs
  set hn : E3 → ℝ := s.indicator h with hn_eq
  have hsmeas : MeasurableSet s := by rw [hs]; exact measurableSet_closedBall
  have hhn : Integrable hn (volume : Measure E3) := by
    rw [hn_eq]; exact hh.integrable_indicator hsmeas
  -- the truncated and the original kernel agree pointwise
  have hreal : ∀ a b : E3,
      Submission.BoseGases.wPairC ℓ h a b = Submission.BoseGases.wPairC ℓ hn a b := by
    intro a b
    simp only [Submission.BoseGases.wPairC_apply, Submission.BoseGases.wScaled]
    by_cases ha : Submission.BoseGases.chiScale ℓ a = 0
    · simp [ha]
    · by_cases hb : Submission.BoseGases.chiScale ℓ b = 0
      · simp [hb]
      · have hmem : a - b ∈ s := by
          have h1 := Submission.BoseGases.chiScale_support_le hℓ ha
          have h2 := Submission.BoseGases.chiScale_support_le hℓ hb
          rw [hs, Metric.mem_closedBall, dist_eq_norm]
          calc ‖a - b - 0‖ = ‖a - b‖ := by rw [sub_zero]
            _ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
            _ ≤ ℓ / 2 + ℓ / 2 := add_le_add h1 h2
            _ = ℓ := by ring
        rw [hn_eq, Set.indicator_of_mem hmem]
  have hkey : ∀ a b : E3, ‖Submission.BoseGases.wPairC ℓ h a b‖ₑ
      = ‖Submission.BoseGases.wPairC ℓ hn a b‖ₑ := by
    intro a b
    rw [hreal a b]
  have hmeas : AEStronglyMeasurable
      (fun p : E3 × E3 => Submission.BoseGases.wPairC ℓ hn p.1 p.2)
      ((volume : Measure E3).prod (volume : Measure E3)) :=
    Work.BoseFixB2.Pot.aemeasurable_wPairC_prod hhn.aestronglyMeasurable
  -- `∫ z, |hₙ z| = ∫ z in closedBall 0 ℓ, |h z|`
  have habs : (∫ z : E3, |hn z|) = ∫ z in s, |h z| := by
    have hpt : (fun z : E3 => |hn z|) = s.indicator (fun z => |h z|) := by
      funext z
      rw [hn_eq]
      by_cases hz : z ∈ s
      · simp [Set.indicator_of_mem hz]
      · simp [Set.indicator_of_notMem hz]
    rw [hpt, MeasureTheory.integral_indicator hsmeas]
  calc (∫⁻ a : E3, (∫⁻ b : E3, ‖Submission.BoseGases.wPairC ℓ h a b‖ₑ)
        ∂(volume.restrict (Submission.BoseGases.acube ℓ)))
      = ∫⁻ a : E3, (∫⁻ b : E3, ‖Submission.BoseGases.wPairC ℓ hn a b‖ₑ)
        ∂(volume.restrict (Submission.BoseGases.acube ℓ)) := by
        apply lintegral_congr
        intro a
        apply lintegral_congr
        intro b
        exact hkey a b
    _ ≤ ∫⁻ a : E3, (∫⁻ b : E3, ‖Submission.BoseGases.wPairC ℓ hn a b‖ₑ)
        ∂(volume : Measure E3) := by
        refine (lintegral_mono_set (Set.subset_univ (Submission.BoseGases.acube ℓ))).trans ?_
        exact le_of_eq (by simp [Measure.restrict_univ])
    _ = ∫⁻ p : E3 × E3, ‖Submission.BoseGases.wPairC ℓ hn p.1 p.2‖ₑ
        ∂((volume : Measure E3).prod (volume : Measure E3)) := by
        rw [MeasureTheory.lintegral_prod (fun p : E3 × E3 =>
          ‖Submission.BoseGases.wPairC ℓ hn p.1 p.2‖ₑ) hmeas.enorm]
    _ ≤ ENNReal.ofReal (ℓ ^ 3 * ∫ z : E3, |hn z|) :=
        Work.BoseFixB2.Pot.lintegral_wPairC_le hℓ hhn
    _ = ENNReal.ofReal (ℓ ^ 3 * ∫ z in Metric.closedBall 0 ℓ, |h z|) := by
        rw [habs, hs]

end Work.BoseFixR
