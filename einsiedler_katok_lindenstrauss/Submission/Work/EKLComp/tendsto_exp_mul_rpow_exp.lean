import Mathlib

namespace Work.EKLComp

theorem tendsto_exp_mul_rpow_exp {f : ℕ → ℝ} (hf : Filter.Tendsto f Filter.atTop Filter.atTop) {ε b d : ℝ}
    (hε : 0 < ε) (hbd : b < d) :
    Filter.Tendsto (fun N : ℕ => Real.exp (3 * b * f N) * (2 * (ε * Real.exp (-(3 * f N)))) ^ d)
      Filter.atTop (nhds 0) := by
  -- Rewrite the term pointwise as `(2 * ε) ^ d * exp (3 * (b - d) * f N)`.
  have key : ∀ N : ℕ, Real.exp (3 * b * f N) * (2 * (ε * Real.exp (-(3 * f N)))) ^ d
      = (2 * ε) ^ d * Real.exp (3 * (b - d) * f N) := by
    intro N
    have h2e : (0:ℝ) ≤ 2 * ε := by positivity
    have hexp : (0:ℝ) ≤ Real.exp (-(3 * f N)) := (Real.exp_pos _).le
    have hbase : 2 * (ε * Real.exp (-(3 * f N))) = (2 * ε) * Real.exp (-(3 * f N)) := by ring
    calc Real.exp (3 * b * f N) * (2 * (ε * Real.exp (-(3 * f N)))) ^ d
        = Real.exp (3 * b * f N) * ((2 * ε) ^ d * (Real.exp (-(3 * f N))) ^ d) := by
            rw [hbase, Real.mul_rpow h2e hexp]
      _ = (2 * ε) ^ d * (Real.exp (3 * b * f N) * (Real.exp (-(3 * f N))) ^ d) := by ring
      _ = (2 * ε) ^ d * (Real.exp (3 * b * f N) * Real.exp (-(3 * f N) * d)) := by
            rw [← Real.exp_mul]
      _ = (2 * ε) ^ d * Real.exp (3 * b * f N + (-(3 * f N)) * d) := by rw [Real.exp_add]
      _ = (2 * ε) ^ d * Real.exp (3 * (b - d) * f N) := by
            rw [show 3 * b * f N + (-(3 * f N)) * d = 3 * (b - d) * f N by ring]
  -- `3 * (b - d) < 0`, so `3 * (b - d) * f N → atBot` and its exponential `→ 0`.
  have hc : 3 * (b - d) < 0 := by nlinarith
  have h2 : Filter.Tendsto (fun N : ℕ => 3 * (b - d) * f N) Filter.atTop Filter.atBot :=
    hf.const_mul_atTop_of_neg hc
  have h3 : Filter.Tendsto (fun N : ℕ => Real.exp (3 * (b - d) * f N)) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h2
  have h4 : Filter.Tendsto (fun N : ℕ => (2 * ε) ^ d * Real.exp (3 * (b - d) * f N))
      Filter.atTop (nhds 0) := by
    have h := h3.const_mul ((2 * ε) ^ d)
    simpa using h
  exact h4.congr (fun N => (key N).symm)

end Work.EKLComp
