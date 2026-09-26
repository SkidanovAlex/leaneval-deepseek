import Mathlib
import Submission.Work.Asymptotics.abs_pow_mul_exp_le

namespace Work.Asymptotics

/-- A polynomial in `r` times the Gaussian `e^{-π r²}` is bounded on the whole real line.

We split at `|r| = 1`.  On `|r| ≤ 1` the factors `|r|^k`, `(1+|r|)^M` and the Gaussian are
each `≤ 1`, `≤ 2^M` and `≤ 1`.  On `|r| ≥ 1` we use `(1+|r|)^M ≤ (2|r|)^M = 2^M |r|^M`, so
the expression is at most `2^M · |r|^{k+M} e^{-π r²}`, which is bounded by the paper's
elementary Gaussian maximum `Work.Asymptotics.abs_pow_mul_exp_le` (taken with `t = 1`). -/
theorem poly_mul_gaussian_bounded (k M : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
    |r| ^ k * (1 + |r|) ^ M * Real.exp (-(Real.pi * r ^ 2)) ≤ C := by
  refine ⟨max ((2:ℝ)^M)
      ((2:ℝ)^M * (((k + M : ℕ) : ℝ) / (2 * Real.pi * Real.exp 1)) ^ (((k + M : ℕ) : ℝ) / 2)),
    ?_, ?_⟩
  · exact le_max_of_le_left (pow_nonneg (by norm_num) M)
  · intro r
    have hgauss : |r| ^ (k + M) * Real.exp (-(Real.pi * r ^ 2))
        ≤ (((k + M : ℕ) : ℝ) / (2 * Real.pi * Real.exp 1)) ^ (((k + M : ℕ) : ℝ) / 2) := by
      have h := abs_pow_mul_exp_le (k + M) (by norm_num : (0:ℝ) < 1) r
      simpa using h
    rcases le_or_gt |r| 1 with hle | hgt
    · have h1 : |r| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg r) hle
      have h2 : (1 + |r|) ^ M ≤ (2:ℝ)^M :=
        pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1 + |r|) (by linarith : 1 + |r| ≤ 2) M
      have h3 : Real.exp (-(Real.pi * r ^ 2)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ Real.pi * r ^ 2 := mul_nonneg Real.pi_pos.le (sq_nonneg r)
        linarith
      calc |r| ^ k * (1 + |r|) ^ M * Real.exp (-(Real.pi * r ^ 2))
          ≤ 1 * (2:ℝ)^M * 1 := by
            apply mul_le_mul (mul_le_mul h1 h2 (by positivity) (by norm_num)) h3
              (Real.exp_nonneg _) (by positivity)
        _ = (2:ℝ)^M := by ring
        _ ≤ max ((2:ℝ)^M)
              ((2:ℝ)^M * (((k + M : ℕ) : ℝ) / (2 * Real.pi * Real.exp 1)) ^
                (((k + M : ℕ) : ℝ) / 2)) :=
            le_max_left _ _
    · have h3 : (1 + |r|) ^ M ≤ (2:ℝ)^M * |r|^M := by
        have h4 : (1 + |r|) ^ M ≤ ((2:ℝ) * |r|)^M :=
          pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1 + |r|)
            (by linarith : 1 + |r| ≤ 2 * |r|) M
        rwa [mul_pow] at h4
      calc |r| ^ k * (1 + |r|) ^ M * Real.exp (-(Real.pi * r ^ 2))
          ≤ |r| ^ k * ((2:ℝ)^M * |r|^M) * Real.exp (-(Real.pi * r ^ 2)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left h3 (by positivity)) le_rfl
              (Real.exp_nonneg _) (by positivity)
        _ = (2:ℝ)^M * (|r| ^ (k + M) * Real.exp (-(Real.pi * r ^ 2))) := by
            rw [pow_add]; ring
        _ ≤ (2:ℝ)^M * (((k + M : ℕ) : ℝ) / (2 * Real.pi * Real.exp 1)) ^
              (((k + M : ℕ) : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hgauss (by positivity)
        _ ≤ max ((2:ℝ)^M)
              ((2:ℝ)^M * (((k + M : ℕ) : ℝ) / (2 * Real.pi * Real.exp 1)) ^
                (((k + M : ℕ) : ℝ) / 2)) :=
            le_max_right _ _

end Work.Asymptotics
