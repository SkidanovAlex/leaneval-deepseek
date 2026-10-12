import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Smear.meanSq3dH
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B.MeanSqPiece

open scoped ENNReal in
theorem meanSq3dCond
    (Hone : ∀ {ℓ h : ℝ}, 0 < h → h ≤ ℓ → ∀ {F : ℝ → ℝ≥0∞},
      AEMeasurable F (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      ∫⁻ u : ℝ, ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x)
          / (MeasureTheory.volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
        ≤ ENNReal.ofReal (9 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2)
    {ℓ h : ℝ} (hh : 0 < h) (hhℓ : h ≤ ℓ) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ u : Fin 3 → ℝ,
        ((∫⁻ y in Work.BoseFixB1S.slBox ℓ h u, F y)
          / (MeasureTheory.volume (Work.BoseFixB1S.slBox ℓ h u))) ^ 2
      ≤ ENNReal.ofReal ((9 / h) ^ 3) * ∫⁻ y in Work.BoseFixB1S.slBig ℓ, (F y) ^ 2 :=
  -- The three-dimensional tensorisation of the one-dimensional bound is already carried out in
  -- the corpus as `Work.BoseFixB1.Smear.meanSq3dH` (screen: `Submission/Work/BoseFixB1/Smear/`
  -- `meanSq3dH.lean`), which proves exactly this inequality at a *fixed* pair `(ℓ, h)` from the
  -- one-dimensional input at that same pair.  Our `Hone` is the one-dimensional input with the
  -- pair universally quantified, so it specialises to the shape `meanSq3dH` asks for.
  Work.BoseFixB1.Smear.meanSq3dH hh hhℓ (fun {_F} hF' => Hone hh hhℓ hF') hF

end Work.BoseFixB1B.MeanSqPiece
