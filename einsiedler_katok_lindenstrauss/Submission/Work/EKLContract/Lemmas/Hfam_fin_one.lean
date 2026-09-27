import Mathlib
import Submission.Work.EKLContract.Interfaces

namespace Work.EKLContract.Lemmas

/-- The Shannon entropy `Hfam` of the constant family of full sets `Set.univ` indexed by `Fin n`
equals `n` times the entropy of the single full set.  Immediate from the definition of `Hfam` as a
sum of a constant family. -/
theorem Hfam_fin_one (X : Type*) [MeasurableSpace X] (μ : MeasureTheory.Measure X) (n : ℕ) : Work.EKLContract.Hfam μ (fun _ : Fin n => (Set.univ : Set X)) = (n : ℝ) * Real.negMulLog (μ Set.univ).toReal := by
  simp [Work.EKLContract.Hfam]

end Work.EKLContract.Lemmas
