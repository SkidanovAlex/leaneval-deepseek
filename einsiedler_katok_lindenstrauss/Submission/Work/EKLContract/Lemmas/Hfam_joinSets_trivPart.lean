import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Consistency

namespace Work.EKLContract.Lemmas

/-- Shannon entropy of the iterated join along the trivial (one-part) partition: the join has a
single part, `Set.univ`, so `Hfam` is the single term `-μ(univ) log μ(univ)`. -/
theorem Hfam_joinSets_trivPart (X : Type*) [MeasurableSpace X] (μ : MeasureTheory.Measure X) (T : X → X) (N : ℕ) : Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T (Work.EKLContract.trivPart X) N) = Real.negMulLog (μ Set.univ).toReal := by
  rw [Work.EKLContract.Hfam]
  simp only [Work.EKLContract.joinSets_trivPart_apply]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Work.EKLContract.trivPart_n]
  simp

end Work.EKLContract.Lemmas
