import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.SmallBoxA0.abox2_lintegral_sub_eq
import Submission.Work.SmallBoxA0.fibre_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory
open scoped ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma lintegral_sub_sq_le {s : ℝ} (hs : 0 < s)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : Measurable g)
    (hint : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (g z) ^ 2)) :
    (∫⁻ p in Submission.BoseGases.abox 2 s,
        ENNReal.ofReal ((g (p 0 - p 1)) ^ 2))
      ≤ ENNReal.ofReal (s ^ 3 * (∫ z : EuclideanSpace ℝ (Fin 3), (g z) ^ 2)) := by
  have hsq_nonneg : (0 : ℝ) ≤ s ^ 3 := by positivity
  rw [abox2_lintegral_sub_eq (s := s) hg]
  calc ∫⁻ x in Submission.BoseGases.acube s,
          ∫⁻ y in Submission.BoseGases.acube s, ENNReal.ofReal ((g (x - y)) ^ 2)
      ≤ ∫⁻ x in Submission.BoseGases.acube s,
          ENNReal.ofReal (∫ z : ℝ³, (g z) ^ 2) := by
        refine lintegral_mono (fun x => ?_)
        exact fibre_bound hs hg hint x
    _ = ENNReal.ofReal (∫ z : ℝ³, (g z) ^ 2) * ENNReal.ofReal (s ^ 3) := by
        rw [lintegral_const, Measure.restrict_apply_univ,
          Submission.BoseGases.acube_volume s hs.le]
    _ = ENNReal.ofReal (s ^ 3 * ∫ z : ℝ³, (g z) ^ 2) := by
        rw [ENNReal.ofReal_mul hsq_nonneg]
        exact mul_comm _ _

end Work.SmallBoxA0
