import Mathlib
import Submission.Work.LinnikAreas.summableNormOfWeyl

namespace Work.LinnikAreas

/-- If `z 0 ≠ 0`, the terms of `z` are bounded by `‖z 0‖`, and
`∑ ‖z n‖ / (‖z 0‖ + ‖z n‖)` converges, then the sequence of `j`-th powers
`(z n) ^ j` is summable for every `j ≥ 1`. -/
theorem summablePowOfWeyl (z : ℕ → ℂ) (hz : z 0 ≠ 0)
    (hle : ∀ n : ℕ, ‖z n‖ ≤ ‖z 0‖)
    (hsum : Summable fun n : ℕ => ‖z n‖ / (‖z 0‖ + ‖z n‖))
    (j : ℕ) (hj : 1 ≤ j) : Summable fun n : ℕ => (z n) ^ j := by
  have hnorm : Summable fun n : ℕ => ‖z n‖ :=
    summableNormOfWeyl z hz hle hsum
  have hbdd : ∀ᶠ n in Filter.atTop, ‖z n‖ ≤ 1 :=
    hnorm.tendsto_atTop_zero.eventually_le_const zero_lt_one
  have hev : ∀ᶠ n in Filter.cofinite, ‖(z n) ^ j‖ ≤ ‖z n‖ := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hbdd] with n hn
    rw [norm_pow]
    exact pow_le_of_le_one (norm_nonneg _) hn (by omega)
  exact Summable.of_norm_bounded_eventually hnorm hev

end Work.LinnikAreas
