import Mathlib.MeasureTheory.Integral.Pi

namespace Commons.Analysis.Measure

theorem integrable_fin_prod {a : ℝ → ℝ} (ha : MeasureTheory.Integrable a (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (n : ℕ) :
    MeasureTheory.Integrable (fun T : Fin n → ℝ => ∏ j, a (T j))
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) := by
  have h1 : MeasureTheory.Integrable (fun T : Fin n → ℝ => ∏ j, a (T j))
      (MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure ℝ))) :=
    MeasureTheory.Integrable.fintype_prod (fun _ : Fin n => ha)
  simpa only [MeasureTheory.volume_pi] using h1

end Commons.Analysis.Measure