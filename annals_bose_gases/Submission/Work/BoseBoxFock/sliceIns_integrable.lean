import Mathlib.CategoryTheory.Countable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.sliceDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The slicing product measure is the Lebesgue measure restricted to the product box
`(boxL ℓ × boxL ℓ) × boxPiSet ι ℓ`. -/
lemma sliceProdMeasure_eq_restrict {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) :
    ((boxMeas ℓ).prod (boxMeas ℓ)).prod
        (Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ))
      = (volume : Measure ((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3))).restrict
          ((Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)
            ×ˢ boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ) := by
  have h1 : (boxMeas ℓ).prod (boxMeas ℓ)
      = (volume : Measure (E3 × E3)).restrict
          (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) := by
    rw [boxMeas, Measure.prod_restrict]
    rw [← Measure.volume_eq_prod]
  have h2 : Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => boxMeas ℓ)
      = (volume : Measure ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)).restrict
          (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ) :=
    (restrict_boxPiSet_eq).symm
  rw [h1, h2, Measure.prod_restrict]
  rw [← Measure.volume_eq_prod]

/-- The product box `(boxL ℓ × boxL ℓ) × boxPiSet ι ℓ` is compact for `0 < ℓ`. -/
lemma isCompact_sliceBox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) :
    IsCompact ((Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)
      ×ˢ boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ) :=
  ((Work.BoseK15.corpusBox.boxL_compact ℓ).prod
    (Work.BoseK15.corpusBox.boxL_compact ℓ)).prod (isCompact_boxPiSet hℓ)

theorem sliceIns_integrable {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {f : Work.BoseDict.Xn n → ℝ} (hf : Continuous f) :
    MeasureTheory.Integrable
      (fun w : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) ×
          ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → EuclideanSpace ℝ (Fin 3)) =>
          f (Work.BoseBoxFock.insertCoord2 p w.1.1 w.1.2 w.2))
      (((Work.BoseBoxFock.boxMeas ℓ).prod (Work.BoseBoxFock.boxMeas ℓ)).prod
        (MeasureTheory.Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} =>
          Work.BoseBoxFock.boxMeas ℓ))) := by
  rw [sliceProdMeasure_eq_restrict p]
  refine ContinuousOn.integrableOn_compact (isCompact_sliceBox hℓ p) ?_
  exact (hf.comp (continuous_sliceInsFun p hp)).continuousOn

end Work.BoseBoxFock
