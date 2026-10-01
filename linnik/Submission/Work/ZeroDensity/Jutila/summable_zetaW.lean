import Mathlib
import Submission.Work.ZeroDensity.Jutila.JutilaDefs

namespace Work.ZeroDensity.Jutila

/-- For `σ > 1` the series `∑_{n} (log n) · n^{-σ}` (the Dirichlet series of `log`, i.e. `-ζ'(σ)`)
converges: `log n` grows slower than any positive power of `n`, so the summand is dominated by a
convergent `p`-series. -/
theorem summable_zetaW (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => Real.log n * (n : ℝ) ^ (-σ)) := by
  set ε : ℝ := (σ - 1) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hσε : 1 < σ - ε := by rw [hεdef]; linarith
  refine Summable.of_nonneg_of_le (f := fun n : ℕ => (1 / ε) * (n : ℝ) ^ (-(σ - ε))) ?_ ?_ ?_
  · intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [Real.log_zero]
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact mul_nonneg (Real.log_nonneg hn1) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      push_cast
      rw [Real.log_zero, zero_mul]
      exact mul_nonneg (div_nonneg zero_le_one hε.le) (Real.rpow_nonneg le_rfl _)
    · have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hpownn : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg hpos.le _
      calc Real.log (n : ℝ) * (n : ℝ) ^ (-σ)
          ≤ ((n : ℝ) ^ ε / ε) * (n : ℝ) ^ (-σ) :=
            mul_le_mul_of_nonneg_right (Real.log_natCast_le_rpow_div n hε) hpownn
        _ = (1 / ε) * ((n : ℝ) ^ ε * (n : ℝ) ^ (-σ)) := by ring
        _ = (1 / ε) * (n : ℝ) ^ (-(σ - ε)) := by
            rw [← Real.rpow_add hpos, show ε + (-σ) = -(σ - ε) by ring]
  · have hlt : -(σ - ε) < -1 := by linarith
    exact ((Real.summable_nat_rpow (p := -(σ - ε))).mpr hlt).mul_left (1 / ε)

end Work.ZeroDensity.Jutila
