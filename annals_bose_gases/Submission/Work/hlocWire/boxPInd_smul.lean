import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.A.cnPlusBoxB_const_eq_of_mem_farSet
import Submission.Work.UBBInputs8.A.cnPlusBoxB_const_farSet_le_tBwordB
import Submission.Work.UBBInputs8.A.exists_hlow_localised_of_bounded
import Submission.Work.UBBInputs8.A.qLHSwordB_integral_u_box
import Submission.Work.UBBInputs8.A.tBLocalisationInd_const
import Submission.Work.UBBInputs8.A.tBwordBInd_const_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.hlocWire

/-- FS's box condensate projection with the box indicator, `boxPInd volA A i Φ = fun x => (1/volA) * (∫ z in A, Φ (update x i z)) * A.indicator 1 (x i)`, is linear in the state; this records its one scaling step. -/
theorem boxPInd_smul {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) (c : ℝ) :
    Work.UBBInputs8.boxPInd volA A i (c • Φ) = c • Work.UBBInputs8.boxPInd volA A i Φ := by
  ext x
  simp only [Work.UBBInputs8.boxPInd, Pi.smul_apply, smul_eq_mul]
  rw [MeasureTheory.integral_const_mul]
  ring

end Work.hlocWire
