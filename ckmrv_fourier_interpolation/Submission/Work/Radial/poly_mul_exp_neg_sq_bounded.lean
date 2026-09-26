import Mathlib

open Filter
open scoped Topology

namespace Work.Radial

/-- A polynomial (with a natural power of `1+t`) times a Gaussian is bounded above on `[0,∞)`. -/
lemma poly_mul_exp_neg_sq_bounded (a : ℝ) (ha : 0 < a) (k m : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → t ^ k * (1 + t) ^ (2 * m) * Real.exp (-a * t ^ 2) ≤ C := by
  -- The function is continuous.
  have hcont : Continuous fun t : ℝ => t ^ k * (1 + t) ^ (2 * m) * Real.exp (-a * t ^ 2) := by
    fun_prop
  -- The auxiliary function `t ↦ t^(k+2m) * exp(-a t^2)` decays to `0` at `+∞`.
  have hdec : Tendsto (fun t : ℝ => t ^ (k + 2 * m) * Real.exp (-a * t ^ 2)) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun t : ℝ => t ^ (k + 2 * m) * Real.exp (-a * t))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact mul_nonneg (pow_nonneg ht _) (Real.exp_pos _).le
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have hle : Real.exp (-a * t ^ 2) ≤ Real.exp (-a * t) := by
        apply Real.exp_le_exp.mpr
        have hsq : t ≤ t ^ 2 := by
          calc t = t * 1 := by ring
            _ ≤ t * t := mul_le_mul_of_nonneg_left ht (by linarith)
            _ = t ^ 2 := by ring
        linarith [mul_le_mul_of_nonneg_left hsq ha.le]
      exact mul_le_mul_of_nonneg_left hle (pow_nonneg (by linarith) _)
    · have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k + 2 * m : ℕ) : ℝ) a ha
      simpa only [Real.rpow_natCast] using this
  -- Hence the original function tends to `0` at `+∞` as well.
  have hftend :
      Tendsto (fun t : ℝ => t ^ k * (1 + t) ^ (2 * m) * Real.exp (-a * t ^ 2)) atTop (𝓝 0) := by
    apply squeeze_zero'
      (g := fun t : ℝ => 2 ^ (2 * m) * (t ^ (k + 2 * m) * Real.exp (-a * t ^ 2)))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact mul_nonneg (mul_nonneg (pow_nonneg ht k) (pow_nonneg (by linarith) (2 * m)))
        (Real.exp_pos _).le
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have h1 : (1 + t) ^ (2 * m) ≤ (2 * t) ^ (2 * m) :=
        pow_le_pow_left₀ (by linarith) (by linarith) (2 * m)
      have h2 : t ^ k * (1 + t) ^ (2 * m) * Real.exp (-a * t ^ 2) ≤
                t ^ k * (2 * t) ^ (2 * m) * Real.exp (-a * t ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left h1 (pow_nonneg (by linarith) k)
      calc t ^ k * (1 + t) ^ (2 * m) * Real.exp (-a * t ^ 2)
          ≤ t ^ k * (2 * t) ^ (2 * m) * Real.exp (-a * t ^ 2) := h2
        _ = 2 ^ (2 * m) * (t ^ (k + 2 * m) * Real.exp (-a * t ^ 2)) := by
              rw [mul_pow, pow_add]; ring
    · simpa using hdec.const_mul (2 ^ (2 * m))
  -- So it is eventually bounded by `1`.
  have hev : ∀ᶠ t in atTop, t ^ k * (1 + t) ^ (2 * m) * Real.exp (-a * t ^ 2) ≤ 1 := by
    filter_upwards [hftend.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with t ht
    exact le_of_lt ht
  rw [Filter.eventually_atTop] at hev
  obtain ⟨R, hR⟩ := hev
  -- On the compact interval `[0, max R 0]` the function attains a maximum.
  obtain ⟨x, _hx, hxmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (le_max_right R 0)) hcont.continuousOn
  refine ⟨max (x ^ k * (1 + x) ^ (2 * m) * Real.exp (-a * x ^ 2)) 1, fun t ht => ?_⟩
  by_cases h : t ≤ max R 0
  · exact (hxmax ⟨ht, h⟩).trans (le_max_left _ _)
  · rw [not_le] at h
    exact (hR t (le_of_lt (lt_of_le_of_lt (le_max_left R 0) h))).trans (le_max_right _ _)

end Work.Radial
