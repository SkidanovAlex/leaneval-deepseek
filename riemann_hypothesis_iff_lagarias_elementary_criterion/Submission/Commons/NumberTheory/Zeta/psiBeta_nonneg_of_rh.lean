import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeroSum_finset_le_beta

namespace Commons.NumberTheory.Zeta

theorem psiBeta_nonneg_of_rh (h : RiemannHypothesis) :
    0 ≤ 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
  have h0 := zeroSum_finset_le_beta h 0 le_rfl (∅ : Finset ℂ) (by simp)
  simpa using h0

end Commons.NumberTheory.Zeta
