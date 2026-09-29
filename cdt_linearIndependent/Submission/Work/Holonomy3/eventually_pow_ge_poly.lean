import Mathlib

namespace Work.Holonomy3

/-- For `1 < r` and any `N`, the exponential `r ^ d` eventually dominates the polynomial
`((d : ℝ) + 1) ^ N`. -/
lemma eventually_pow_ge_poly (r : ℝ) (hr : 1 < r) (N : ℕ) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ((d : ℝ) + 1) ^ N ≤ r ^ d := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hlog : 0 < Real.log r := Real.log_pos hr
  -- `d ^ N = o(exp (log r * d))`, hence also for the constant multiple `2 ^ N * d ^ N`.
  have hmain : (fun d : ℕ => (2 : ℝ) ^ N * (d : ℝ) ^ N) =o[Filter.atTop]
      (fun d : ℕ => Real.exp (Real.log r * d)) := by
    have h1 : (fun x : ℝ => x ^ N) =o[Filter.atTop]
        (fun x : ℝ => Real.exp (Real.log r * x)) :=
      isLittleO_pow_exp_pos_mul_atTop N hlog
    have h2 : (fun d : ℕ => (d : ℝ) ^ N) =o[Filter.atTop]
        (fun d : ℕ => Real.exp (Real.log r * d)) :=
      h1.comp_tendsto tendsto_natCast_atTop_atTop
    exact h2.const_mul_left _
  have hev := (Asymptotics.isLittleO_iff.1 hmain one_pos)
  obtain ⟨d₁, hd₁⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max d₁ 1, fun d hd => ?_⟩
  have hd1 : d₁ ≤ d := le_trans (le_max_left _ _) hd
  have hd1' : 1 ≤ d := le_trans (le_max_right _ _) hd
  have hbound := hd₁ d hd1
  have hb : (2 : ℝ) ^ N * (d : ℝ) ^ N ≤ r ^ d := by
    rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ N * (d : ℝ) ^ N),
      Real.norm_of_nonneg (Real.exp_pos _).le, one_mul] at hbound
    rw [mul_comm (Real.log r) (d : ℝ), Real.exp_nat_mul, Real.exp_log hr0] at hbound
    exact hbound
  have hstep : ((d : ℝ) + 1) ^ N ≤ (2 : ℝ) ^ N * (d : ℝ) ^ N := by
    have hle : (d : ℝ) + 1 ≤ 2 * (d : ℝ) := by
      have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1'
      linarith
    calc ((d : ℝ) + 1) ^ N ≤ (2 * (d : ℝ)) ^ N := by
          apply pow_le_pow_left₀ (by positivity) hle
       _ = 2 ^ N * (d : ℝ) ^ N := by rw [mul_pow]
  linarith

end Work.Holonomy3
