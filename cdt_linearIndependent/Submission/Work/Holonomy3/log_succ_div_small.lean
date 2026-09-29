import Mathlib
import Submission.Work.Holonomy3.log_absorb

namespace Work.Holonomy3

/-- The `log (D+1)/D` term of the sift of the fine holonomy bound: for every `c > 0`, all
sufficiently large `D : ℕ` satisfy `2·log (D+1)/D ≤ c`.  (From
`Work.Holonomy3.eventually_log_mul_le` with `a = 2`: `log (D+1) ≤ log (2D) ≤ (c/4)·D` for
`D ≥ 1`, hence `2 log(D+1)/D ≤ c/2 ≤ c`.) -/
lemma log_succ_div_small {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, ∀ D : ℕ, N ≤ D → 2 * Real.log ((D : ℝ) + 1) / (D : ℝ) ≤ c := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (eventually_log_mul_le (a := 2) (ε := c / 4) (by norm_num) (by linarith))
  refine ⟨max N 1, fun D hD => ?_⟩
  have hD1 : 1 ≤ D := le_trans (le_max_right _ _) hD
  have hND : N ≤ D := le_trans (le_max_left _ _) hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD1
  have hDR1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hlog : Real.log (2 * (D : ℝ)) ≤ (c / 4) * (D : ℝ) := hN D hND
  have hmono : Real.log ((D : ℝ) + 1) ≤ Real.log (2 * (D : ℝ)) := by
    apply Real.log_le_log (by positivity)
    linarith
  have h2 : 2 * Real.log ((D : ℝ) + 1) ≤ 2 * ((c / 4) * (D : ℝ)) := by
    nlinarith [hmono, hlog]
  rw [div_le_iff₀ hDpos]
  nlinarith [h2]

end Work.Holonomy3
