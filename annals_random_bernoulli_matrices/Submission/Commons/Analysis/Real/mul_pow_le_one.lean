import Mathlib
import Submission.Commons.Analysis.Real.exists_geom_pow_le_one_div

namespace Commons.Analysis.Real

theorem mul_pow_le_one {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {c : ℝ} (hc : 0 ≤ c) :
    ∃ N : ℕ, ∀ n ≥ N, c * s ^ n ≤ 1 := by
  rcases le_or_gt c 1 with hc1 | hc1
  · exact ⟨0, fun n _ => by
      have hsn : s ^ n ≤ 1 := pow_le_one₀ (le_of_lt hs0) (le_of_lt hs1)
      calc c * s ^ n ≤ 1 * s ^ n :=
            mul_le_mul_of_nonneg_right hc1 (pow_nonneg (le_of_lt hs0) n)
        _ ≤ 1 := by simpa using hsn⟩
  · obtain ⟨q, _, hq⟩ := exists_geom_pow_le_one_div hs0 hs1 (le_of_lt hc1)
    refine ⟨q, fun n hn => ?_⟩
    have hsq : s ^ n ≤ s ^ q :=
      pow_le_pow_of_le_one (le_of_lt hs0) (le_of_lt hs1) hn
    have hcne : c ≠ 0 := ne_of_gt (lt_trans zero_lt_one hc1)
    calc c * s ^ n ≤ c * s ^ q := mul_le_mul_of_nonneg_left hsq hc
      _ ≤ c * (1 / c) := mul_le_mul_of_nonneg_left hq hc
      _ = 1 := by field_simp

end Commons.Analysis.Real
