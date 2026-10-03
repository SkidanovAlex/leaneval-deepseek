import Mathlib
import Submission.Work.Analysis.EndVar.Defs

namespace Work.KMTAreas.A4

/-- The logarithmic scale `Log N = log₂ max(N,2)` satisfies `2^{Log N} ≤ 2N` for `N ≥ 1`. -/
theorem two_pow_logN_le {N : ℕ} (hN : 1 ≤ N) : (2 : ℝ) ^ Work.Analysis.EndVar.logN N ≤ 2 * (N : ℝ) := by
  have hpow : (2 : ℝ) ^ (Nat.log 2 (max N 2)) ≤ ((max N 2 : ℕ) : ℝ) := by
    have h := Nat.pow_log_le_self 2 (by omega : max N 2 ≠ 0)
    exact_mod_cast h
  have hmax : ((max N 2 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    rw [Nat.cast_max]
    have h1 : (N : ℝ) ≤ 2 * (N : ℝ) := by
      have : (0 : ℝ) ≤ (N : ℝ) := by positivity
      linarith
    have h2 : (2 : ℝ) ≤ 2 * (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    exact max_le h1 h2
  calc (2 : ℝ) ^ Work.Analysis.EndVar.logN N = (2 : ℝ) ^ (Nat.log 2 (max N 2)) := by
        simp [Work.Analysis.EndVar.logN]
    _ ≤ ((max N 2 : ℕ) : ℝ) := hpow
    _ ≤ 2 * (N : ℝ) := hmax

end Work.KMTAreas.A4
