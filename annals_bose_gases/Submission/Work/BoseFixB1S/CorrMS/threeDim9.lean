import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.MeanSq.Box3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S.CorrMS

theorem threeDim9 {ℓ h : ℝ} (hh : 0 < h) (hhℓ : h ≤ ℓ)
    (h1d : ∀ {F : ℝ → ENNReal}, AEMeasurable F (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      ∫⁻ u : ℝ, ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x)
          / (MeasureTheory.volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
        ≤ ENNReal.ofReal (9 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2)
    {F : (Fin 3 → ℝ) → ENNReal} (hF : Measurable F) :
    ∫⁻ u : Fin 3 → ℝ, ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y)
        / (MeasureTheory.volume (Work.BoseFixB1S.slBox ℓ h u))) ^ 2
      ≤ ENNReal.ofReal ((9 / h) ^ 3) * ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y) ^ 2 := by sorry

end Work.BoseFixB1S.CorrMS
