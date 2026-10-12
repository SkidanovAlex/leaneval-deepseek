import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

namespace Work.BoseBogFS

/-- The `p`-convention Fourier transform `Ŵ(k) = ∫ e^{−i⟨k,y⟩}W(y)dy` of a real function
(`Work.BoseFixR.chat`, the real part of the corpus's `Submission.BoseGases.kinFT`) at zero
momentum is the plain integral `∫ W`: indeed `kinFT u 0 = ∫ y, u y`, as `e^{−i⟨0,y⟩} = 1`. -/
theorem chat_zero_eq_integral (W : EuclideanSpace ℝ (Fin 3) → ℝ) (hW : MeasureTheory.Integrable W) :
    Work.BoseFixR.chat W 0 = ∫ y : EuclideanSpace ℝ (Fin 3), W y := by
  simp only [Work.BoseFixR.chat, Submission.BoseGases.kinFT, inner_zero_left,
    Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul]
  rw [integral_complex_ofReal]
  exact Complex.ofReal_re _

end Work.BoseBogFS
