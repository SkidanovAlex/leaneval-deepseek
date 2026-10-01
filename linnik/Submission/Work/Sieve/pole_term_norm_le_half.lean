import Mathlib

namespace Work.Sieve

theorem pole_term_norm_le_half {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hsre : s.re = 1/2) :
    ‖((N : ℂ) ^ (1 - s)) / (s - 1)‖ ≤ 2 * ((N : ℝ) ^ (1/2 : ℝ)) := by
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  -- numerator: ‖N^(1-s)‖ = N^((1-s).re) = N^(1/2)
  have hnum : ‖(N : ℂ) ^ (1 - s)‖ = (N:ℝ) ^ (1/2 : ℝ) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos hNpos (1 - s)
    rw [Complex.ofReal_natCast N] at h
    rw [h]
    congr 1
    norm_num [Complex.sub_re, Complex.one_re, hsre]
  -- denominator: ‖s - 1‖ ≥ 1/2
  have hden : (1/2 : ℝ) ≤ ‖s - 1‖ := by
    have hsq : (1/4 : ℝ) ≤ ‖s - 1‖^2 := by
      have h : ‖s - 1‖^2 = (1/2)^2 + (s-1).im^2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        have : (s-1).re = 1/2 - 1 := by simp [Complex.sub_re, hsre]
        rw [this]; ring
      nlinarith [sq_nonneg (s-1).im]
    have h1 := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (norm_nonneg (s-1))] at h1
    norm_num at h1
    exact h1
  rw [norm_div, hnum]
  calc (N:ℝ) ^ (1/2:ℝ) / ‖s - 1‖ ≤ (N:ℝ)^(1/2:ℝ) / (1/2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = 2 * (N:ℝ)^(1/2:ℝ) := by ring

end Work.Sieve
