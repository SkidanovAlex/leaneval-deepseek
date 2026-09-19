import Mathlib.NumberTheory.Chebyshev
import Submission.Commons.NumberTheory.Chebyshev.charSum_lamPrime_diff_bound

namespace Commons.NumberTheory.Chebyshev

theorem lcmUpto_dvd_of_le {m n : ℕ} (h : m ≤ n) : Nat.lcmUpto m ∣ Nat.lcmUpto n := by
  unfold Nat.lcmUpto
  apply Finset.lcm_mono
  intro a ha
  simp at ha ⊢
  omega

end Commons.NumberTheory.Chebyshev