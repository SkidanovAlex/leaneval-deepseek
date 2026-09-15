import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Analysis.Measure

open MeasureTheory

theorem aemeasurable_sub_mul_prod {d : ℕ} {G H : EuclideanSpace ℝ (Fin d) → ENNReal}
    (hG : AEMeasurable G (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hH : AEMeasurable H (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
    AEMeasurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => G (p.2 - p.1) * H p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).prod MeasureTheory.volume) := by
  have hqmp : Measure.QuasiMeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.2 - p.1)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
    refine MeasureTheory.QuasiMeasurePreserving.prod_of_right (measurable_snd.sub measurable_fst) ?_
    filter_upwards with x
    simpa [sub_eq_add_neg] using (measurePreserving_add_right
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) (-x)).quasiMeasurePreserving
  have h1 : AEMeasurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => G (p.2 - p.1))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :=
    hG.comp_quasiMeasurePreserving hqmp
  have h2 : AEMeasurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => H p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :=
    hH.comp_snd
  exact h1.mul h2

end Commons.Analysis.Measure