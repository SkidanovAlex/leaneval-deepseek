import Submission.Work.EKLContract.Consistency
import Submission.Work.EKLContract.Lemmas.Hfam_fin_one
import Submission.Work.EKLContract.Lemmas.Hfam_joinSets_trivPart

/-!
# EKL contract — the entropy objects at the trivial partition

`Consistency.lean` proves the consistency of the entropy objects at a Dirac measure.  This
module adds the same at the one-part partition `trivPart`, using the fleet lemmas
`Lemmas.Hfam_fin_one` and `Lemmas.Hfam_joinSets_trivPart` (which import `Consistency` for the
definition of `trivPart`, hence this file and not `Consistency.lean`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLContract

section Entropy

variable {X : Type*} [mX : MeasurableSpace X]

/-- `h_μ(T,P₀)` for the one-part partition, in closed form. -/
theorem hPart_trivPart (μ : Measure X) (T : X → X) :
    hPart μ T (trivPart X) =
      ⨅ N : ℕ, Real.negMulLog (μ Set.univ).toReal / ((N : ℝ) + 1) := by
  simp only [hPart]
  congr 1
  funext N
  rw [Lemmas.Hfam_joinSets_trivPart]

/-- **The partition entropy of the trivial partition of a probability measure is zero.** -/
theorem hPart_trivPart_eq_zero (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) :
    hPart μ T (trivPart X) = 0 := by
  rw [hPart_trivPart]
  simp

/-- `ofReal` of the trivial-partition entropy. -/
theorem ofReal_hPart_trivPart (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) :
    ENNReal.ofReal (hPart μ T (trivPart X)) = 0 := by
  rw [hPart_trivPart_eq_zero]
  simp

end Entropy

end Work.EKLContract
