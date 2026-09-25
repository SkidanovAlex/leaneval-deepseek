import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.decouple_defs

namespace Work.BourgainPlan.IonescuWainger

theorem transversal_sum_aemeasurable {X : Type*} [MeasurableSpace X] {α : Type*} [DecidableEq α]
    (S : Finset α) (k n : ℕ) (c : S → Fin k) (f : Finset α → X → ℂ) (μ : MeasureTheory.Measure X)
    (hfm : ∀ A, A ⊆ S → A.card ≤ k → AEMeasurable (f A) μ) :
    AEMeasurable (fun x => enorm (∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ n) μ := by
  have hsum : AEMeasurable (fun x => ∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) μ :=
    Finset.aemeasurable_fun_sum _ (fun σ _ => hfm _ (tupleSet_subset S σ) (tupleSet_card_le S σ))
  exact hsum.enorm.pow_const n

end Work.BourgainPlan.IonescuWainger
