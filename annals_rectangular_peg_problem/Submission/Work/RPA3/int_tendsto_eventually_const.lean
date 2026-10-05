import Mathlib

namespace Work.RPA3

/-- A sequence of integers, viewed as a sequence of reals, which converges is eventually constant:
for large `n` two terms are within distance `< 1` of each other, hence equal. -/
theorem int_tendsto_eventually_const {k : ℕ → ℤ} {a : ℝ}
    (h : Filter.Tendsto (fun n => (k n : ℝ)) Filter.atTop (nhds a)) :
    ∃ N : ℕ, ∀ n ≥ N, k n = k N := by
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h (1/2) (by norm_num)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : dist (k n : ℝ) a < 1/2 := hN n hn
  have h2 : dist (k N : ℝ) a < 1/2 := hN N le_rfl
  rw [dist_eq_norm, Real.norm_eq_abs] at h1 h2
  -- Two terms close to the same limit are within distance 1 of each other
  have habs : |(k n : ℝ) - (k N : ℝ)| < 1 := by
    have h3 : |(k n : ℝ) - (k N : ℝ)| ≤ |(k n : ℝ) - a| + |a - (k N : ℝ)| := by
      rw [show (k n : ℝ) - (k N : ℝ) = ((k n : ℝ) - a) + (a - (k N : ℝ)) by ring]
      exact abs_add_le _ _
    have h4 : |a - (k N : ℝ)| < 1/2 := by rwa [abs_sub_comm] at h2
    linarith
  have hlt : (k n : ℝ) - (k N : ℝ) < 1 := (abs_lt.mp habs).2
  have hgt : -1 < (k n : ℝ) - (k N : ℝ) := (abs_lt.mp habs).1
  -- transport to `ℤ`, where the only integer in `(-1, 1)` is `0`
  have hlt' : k n - k N < 1 := by exact_mod_cast hlt
  have hgt' : -1 < k n - k N := by exact_mod_cast hgt
  omega

end Work.RPA3
