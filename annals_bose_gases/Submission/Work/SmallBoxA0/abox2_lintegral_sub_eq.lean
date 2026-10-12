import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxA0.W1L2Infra
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory
open scoped ENNReal


local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem abox2_lintegral_sub_eq {s : ℝ}
    {g : ℝ³ → ℝ} (hg : Measurable g) :
    (∫⁻ p in Submission.BoseGases.abox 2 s, ENNReal.ofReal ((g (p 0 - p 1)) ^ 2))
      = ∫⁻ x in Submission.BoseGases.acube s,
          ∫⁻ y in Submission.BoseGases.acube s, ENNReal.ofReal ((g (x - y)) ^ 2) := by
  let G : ℝ³ × ℝ³ → ℝ≥0∞ := fun q => ENNReal.ofReal ((g (q.1 - q.2)) ^ 2)
  have hG : Measurable G := by
    fun_prop
  calc
    (∫⁻ p in Submission.BoseGases.abox 2 s, ENNReal.ofReal ((g (p 0 - p 1)) ^ 2))
        = ∫⁻ p, G (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ³) p)
            ∂(volume.restrict (Submission.BoseGases.abox 2 s)) := by
          apply lintegral_congr
          intro p
          simp [G, MeasurableEquiv.piFinTwo_apply]
    _ = ∫⁻ q : ℝ³ × ℝ³, G q
            ∂(((volume : Measure ℝ³).restrict (Submission.BoseGases.acube s)).prod
              ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube s))) :=
          (abox2_measurePreserving s).lintegral_comp hG
    _ = ∫⁻ x in Submission.BoseGases.acube s,
          ∫⁻ y in Submission.BoseGases.acube s, G (x, y) := by
          rw [lintegral_prod G hG.aemeasurable]
    _ = ∫⁻ x in Submission.BoseGases.acube s,
          ∫⁻ y in Submission.BoseGases.acube s, ENNReal.ofReal ((g (x - y)) ^ 2) := by
          apply lintegral_congr; intro x
          apply lintegral_congr; intro y
          simp [G]

end Work.SmallBoxA0
