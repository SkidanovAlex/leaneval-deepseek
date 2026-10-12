import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxTBWord

/-- The windowed exponential amplitude `tBamp χ p Ψ i x` of the slot-`i`
fibre does not depend on the slot-`i` coordinate `x i`: it only sees the
other coordinates through `Ψ (x_{i←z})`.  Hence it is unchanged under
`Function.update x i y`. -/
theorem tBamp_indep_slot {N : ℕ} (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p : EuclideanSpace ℝ (Fin 3)) (Ψ : Submission.BoseGases.X N → ℝ) (i : Fin N) (x : Submission.BoseGases.X N) (y : EuclideanSpace ℝ (Fin 3)) : Work.SmallBoxTBWord.tBamp χ p Ψ i (Function.update x i y) = Work.SmallBoxTBWord.tBamp χ p Ψ i x := by
  simp only [Work.SmallBoxTBWord.tBamp, Function.update_idem]

end Work.SmallBoxTBWord
