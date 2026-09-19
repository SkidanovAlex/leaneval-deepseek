import Mathlib.NumberTheory.Harmonic.Bounds
import Submission.Commons.Analysis.ExpLog.log_one_sub_le

namespace Commons.Analysis.ExpLog

/-! `∑_{k=1}^{K} 1/k ≤ 1 + log K` (reals, holds for every natural `K`).
A complete proof already exists in `Submission/ChildDirichletMV.lean`
(`Submission.BoundedMultiplicativeFunctions.sum_inv_Icc_le_log`). -/
lemma sum_inv_Icc_le_log (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, ((k : ℝ))⁻¹) ≤ 1 + Real.log (K : ℝ) := by
  have h := harmonic_le_one_add_log K
  rw [harmonic_eq_sum_Icc] at h
  simpa using h

end Commons.Analysis.ExpLog
