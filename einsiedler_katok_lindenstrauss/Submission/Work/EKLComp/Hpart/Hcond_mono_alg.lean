import Mathlib
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLC6Core.Hcond_mono

namespace Work.EKLComp.Hpart

theorem Hcond_mono_alg {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (P : Work.EKLContract.FinPart X)
    {m₁ m₂ : MeasurableSpace X} (h : m₁ ≤ m₂) :
    @Work.EKLContract.Hcond X mX μ P m₂ ≤ @Work.EKLContract.Hcond X mX μ P m₁ := by
  exact Work.EKLC6Core.Hcond_mono (mX := mX) μ P m₁ m₂ h

end Work.EKLComp.Hpart
