import Mathlib

namespace Work.LinnikAreas.Density4

/-- The increment of `x ↦ (M-1) log x - (log x)^2 / 2` over `[n, n+1]` is bounded by
its derivative at `n`, valid whenever `log n ≤ M - 2`. -/
theorem dls_term_bound (M : ℝ) (n : ℕ) (hn : 1 ≤ n) (hlog : Real.log (n : ℝ) ≤ M - 2) :
    ((M - 1) * Real.log ((n + 1 : ℕ) : ℝ) - (Real.log ((n + 1 : ℕ) : ℝ)) ^ 2 / 2)
      - ((M - 1) * Real.log (n : ℝ) - (Real.log (n : ℝ)) ^ 2 / 2)
    ≤ (M - 1 - Real.log (n : ℝ)) / (n : ℝ) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  -- The key elementary estimate: `log (n+1) - log n ≤ 1/n`.
  have hs : Real.log ((n:ℝ)+1) - Real.log (n:ℝ) ≤ 1/(n:ℝ) := by
    have h1 : Real.log (((n:ℝ)+1)/(n:ℝ)) ≤ ((n:ℝ)+1)/(n:ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at h1
    have : ((n:ℝ)+1)/(n:ℝ) - 1 = 1/(n:ℝ) := by field_simp; ring
    linarith [h1, this]
  -- Rearranged target inequality.
  have key : (M - 1 - Real.log (n:ℝ)) * (Real.log ((n:ℝ)+1) - Real.log (n:ℝ) - 1/(n:ℝ))
      ≤ (Real.log ((n:ℝ)+1) - Real.log (n:ℝ))^2 / 2 := by
    -- `M - 1 - log n ≥ 1` under the hypothesis `log n ≤ M - 2`.
    have hc : 1 ≤ M - 1 - Real.log (n:ℝ) := by linarith [hlog]
    have hsnn : Real.log ((n:ℝ)+1) - Real.log (n:ℝ) - 1/(n:ℝ) ≤ 0 := by linarith
    have hstep : (M - 1 - Real.log (n:ℝ)) * (Real.log ((n:ℝ)+1) - Real.log (n:ℝ) - 1/(n:ℝ))
        ≤ (Real.log ((n:ℝ)+1) - Real.log (n:ℝ) - 1/(n:ℝ)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (neg_nonneg.mpr hsnn)]
    nlinarith [hstep, sq_nonneg (Real.log ((n:ℝ)+1) - Real.log (n:ℝ))]
  push_cast
  have heq : (M - 1) * Real.log (↑n + 1) - Real.log (↑n + 1) ^ 2 / 2
        - ((M - 1) * Real.log ↑n - Real.log ↑n ^ 2 / 2) - (M - 1 - Real.log ↑n) / ↑n
      = (M - 1 - Real.log ↑n) * (Real.log (↑n + 1) - Real.log ↑n - 1 / ↑n)
        - (Real.log (↑n + 1) - Real.log ↑n) ^ 2 / 2 := by ring
  linarith [key, heq]

end Work.LinnikAreas.Density4
