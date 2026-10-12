import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxSliding.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxSliding

lemma bandSet_measure_le {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
    (hAδ : 0 ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ)) :
    (MeasureTheory.volume (Work.SmallBoxSliding.bandSet ℓ d μ)).toReal
      ≤ ((ℓ * d) ^ 3)⁻¹ * (12 * μ ^ (-1 / 3 : ℝ) * ℓ ^ 2 * (1 + d) ^ 2) := by
  have hset : bandSet ℓ d μ = Submission.BoseGases.chiSmallBadBand ℓ d μ := rfl
  rw [hset]
  have hmeas := Submission.BoseGases.chiSmallBadBand_measure_le
    (ℓ := ℓ) (d := d) (μ := μ) hℓ hd hμ hAδ
  have hshell := Submission.BoseGases.chiSmallB_badband_shell_bound
    (ℓ := ℓ) (d := d) (μ := μ) hℓ hd hμ hAδ
  have hc : 0 ≤ ((ℓ * d) ^ 3)⁻¹ := by positivity
  refine ENNReal.toReal_le_of_le_ofReal ?_ ?_
  · have hμp : 0 ≤ μ ^ (-1 / 3 : ℝ) := le_of_lt (Real.rpow_pos_of_pos hμ _)
    have h12 : 0 ≤ 12 * μ ^ (-1 / 3 : ℝ) * ℓ ^ 2 * (1 + d) ^ 2 := by positivity
    exact mul_nonneg hc h12
  · exact le_trans hmeas (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hshell hc))

end Work.SmallBoxSliding
