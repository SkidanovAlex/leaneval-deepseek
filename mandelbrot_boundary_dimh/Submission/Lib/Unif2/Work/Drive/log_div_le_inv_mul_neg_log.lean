import Mathlib

namespace Work.Drive

/-- If `0 < ρ`, `0 < d`, `0 < s`, `s ≤ M` and `M * ρ ^ k ≤ 1` with `1 ≤ k`, then
`log (ρ / d) ≤ (1/k) * (- log (d ^ k * s))`.  Equivalently `ρ ^ k * s ≤ 1`, which
follows from `ρ ^ k * s ≤ ρ ^ k * M = M * ρ ^ k ≤ 1`. -/
theorem log_div_le_inv_mul_neg_log {ρ d s M : ℝ} {k : ℕ}
    (hρ : 0 < ρ) (hd : 0 < d) (hs : 0 < s) (hk : 1 ≤ k)
    (hsM : s ≤ M) (hMρ : M * ρ ^ k ≤ 1) :
    Real.log (ρ / d) ≤ (1 / (k : ℝ)) * (-Real.log (d ^ k * s)) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have h : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hrk : 0 < ρ ^ k := pow_pos hρ k
  have hdk : 0 < d ^ k := pow_pos hd k
  -- The heart: `ρ ^ k * s ≤ 1`.
  have hstep : ρ ^ k * s ≤ 1 := by
    have h1 : ρ ^ k * s ≤ ρ ^ k * M := mul_le_mul_of_nonneg_left hsM (le_of_lt hrk)
    have h2 : ρ ^ k * M ≤ 1 := by
      have h : ρ ^ k * M = M * ρ ^ k := by ring
      rw [h]; exact hMρ
    linarith
  have hlog : Real.log (ρ ^ k * s) ≤ 0 := by
    rw [← Real.log_one]
    exact Real.log_le_log (mul_pos hrk hs) hstep
  -- `log (ρ ^ k * s) = k * log (ρ / d) + log (d ^ k * s)`.
  have hkey : Real.log (ρ ^ k * s) = (k : ℝ) * Real.log (ρ / d) + Real.log (d ^ k * s) := by
    rw [Real.log_mul (ne_of_gt hrk) (ne_of_gt hs), Real.log_pow,
        Real.log_mul (ne_of_gt hdk) (ne_of_gt hs), Real.log_pow,
        Real.log_div (ne_of_gt hρ) (ne_of_gt hd)]
    ring
  have hmain : (k : ℝ) * Real.log (ρ / d) ≤ -Real.log (d ^ k * s) := by
    linarith [hkey ▸ hlog]
  have heq : (1 / (k : ℝ)) * (-Real.log (d ^ k * s))
      = (-Real.log (d ^ k * s)) / (k : ℝ) := by ring
  rw [heq, le_div_iff₀ hkpos]
  linarith [hmain]

end Work.Drive
