import Mathlib
import Submission.Commons.Analysis.ExpLog.harmonic_le_one_add_log
import Submission.Commons.Analysis.ExpLog.log_le_rpow_div

namespace Commons.Analysis.Series

open Finset
open scoped BigOperators

/-- The harmonic sum is dominated by any positive power: for every `e > 0` there is `C > 0`
with `∑_{s=1}^{M} 1/s ≤ C · M^e` for all `M ≥ 1`.  (Indeed `∑_{s≤M} 1/s ≤ 1 + log M` and
`log M ≤ M^e/e`.) -/
theorem harmonic_sum_le_rpow {e : ℝ} (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
      (∑ s ∈ Finset.Icc 1 M, (1:ℝ)/(s:ℝ)) ≤ C * (M:ℝ)^e := by
  refine ⟨1 + 1 / e, by positivity, ?_⟩
  intro M hM
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hsum : (∑ s ∈ Finset.Icc 1 M, (1 : ℝ) / (s : ℝ)) ≤ 1 + Real.log (M : ℝ) :=
    Commons.Analysis.ExpLog.harmonic_le_one_add_log M hM
  have hlog : Real.log (M : ℝ) ≤ (M : ℝ) ^ e / e :=
    Commons.Analysis.ExpLog.log_le_rpow_div hM1 he
  have hpowe : (1 : ℝ) ≤ (M : ℝ) ^ e := Real.one_le_rpow hM1 (le_of_lt he)
  have hkey : (1 : ℝ) + (M : ℝ) ^ e / e ≤ (1 + 1 / e) * (M : ℝ) ^ e := by
    have h1 : (1 : ℝ) + (M : ℝ) ^ e / e ≤ (M : ℝ) ^ e + (M : ℝ) ^ e / e := by linarith
    calc (1 : ℝ) + (M : ℝ) ^ e / e ≤ (M : ℝ) ^ e + (M : ℝ) ^ e / e := h1
      _ = (1 + 1 / e) * (M : ℝ) ^ e := by ring
  calc (∑ s ∈ Finset.Icc 1 M, (1 : ℝ) / (s : ℝ)) ≤ 1 + Real.log (M : ℝ) := hsum
    _ ≤ 1 + (M : ℝ) ^ e / e := by linarith
    _ ≤ (1 + 1 / e) * (M : ℝ) ^ e := hkey

end Commons.Analysis.Series
