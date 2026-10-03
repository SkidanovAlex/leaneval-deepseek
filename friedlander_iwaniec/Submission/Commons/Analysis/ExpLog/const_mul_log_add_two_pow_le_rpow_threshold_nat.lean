import Mathlib
import Submission.Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold

namespace Commons.Analysis.ExpLog

theorem const_mul_log_add_two_pow_le_rpow_threshold_nat {K : ℝ} (hK : 0 ≤ K) {n : ℕ} {r : ℝ}
    (hr : 0 < r) :
    ∃ X : ℕ, 1 ≤ X ∧ ∀ x : ℕ, X ≤ x → K * (Real.log ((x : ℝ) + 2)) ^ n ≤ (x : ℝ) ^ r := by
  have hr2 : 0 < r / 2 := by positivity
  obtain ⟨X₀, hX₀, h⟩ := const_mul_log_pow_le_rpow_threshold hK hr2
  obtain ⟨N, hN⟩ := exists_nat_ge X₀
  refine ⟨max N 2, by omega, ?_⟩
  intro x hx
  have hNx : N ≤ x := le_trans (le_max_left N 2) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right N 2) hx
  have hxX₀ : X₀ ≤ (x : ℝ) + 2 := by
    have h1 : X₀ ≤ (N : ℝ) := hN
    have h2 : (N : ℝ) ≤ (x : ℝ) := by exact_mod_cast hNx
    linarith
  have hx2R : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hstep : ((x : ℝ) + 2) ^ (r / 2) ≤ (x : ℝ) ^ r := by
    have hle : (x : ℝ) + 2 ≤ 2 * (x : ℝ) := by linarith
    have hnn : (0 : ℝ) ≤ (x : ℝ) + 2 := by linarith
    calc
      ((x : ℝ) + 2) ^ (r / 2) ≤ (2 * (x : ℝ)) ^ (r / 2) :=
            Real.rpow_le_rpow hnn hle hr2.le
      _ = (2 : ℝ) ^ (r / 2) * (x : ℝ) ^ (r / 2) :=
            Real.mul_rpow (by norm_num) hxpos.le
      _ ≤ (x : ℝ) ^ (r / 2) * (x : ℝ) ^ (r / 2) := by
            exact mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow (by norm_num) hx2R hr2.le)
              (Real.rpow_nonneg hxpos.le _)
      _ = (x : ℝ) ^ r := by
            rw [← Real.rpow_add hxpos (r / 2) (r / 2)]
            congr 1
            ring
  exact le_trans (h ((x : ℝ) + 2) hxX₀) hstep

end Commons.Analysis.ExpLog
