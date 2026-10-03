import Mathlib
import Submission.Work.Peluse.BoxNorm.boxNormPow_le_one

namespace Work.Peluse.Prop36SW

theorem boxNormPow_le_boxNorm {t : ℕ} {Q : Fin t → Finset ℤ} {S : Finset ℤ} {f : ℤ → ℂ}
    (ht : 1 ≤ t) (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsupp : ∀ x : ℤ, x ∉ S → f x = 0) :
    Work.Peluse.boxNormPow t Q S f ≤ Work.Peluse.boxNorm t Q S f := by
  -- `boxNorm` is by definition the `(1/2^t)`-th power of `boxNormPow`, and `boxNormPow ≤ 1`
  -- for a `1`-bounded function supported in `S`; for `0 ≤ a ≤ 1` and `0 < c ≤ 1` one has
  -- `a ≤ a ^ c`.
  have hle1 : Work.Peluse.boxNormPow t Q S f ≤ 1 :=
    Work.Peluse.BoxNorm.boxNormPow_le_one hf hsupp
  have hnn : 0 ≤ Work.Peluse.boxNormPow t Q S f := norm_nonneg _
  have hcpos : 0 < (1 : ℝ) / ((2 : ℝ) ^ t) := by positivity
  have hcle : (1 : ℝ) / ((2 : ℝ) ^ t) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  unfold Work.Peluse.boxNorm
  rcases eq_or_lt_of_le hnn with h | h
  · rw [← h, Real.zero_rpow (ne_of_gt hcpos)]
  · simpa using Real.rpow_le_rpow_of_exponent_ge h hle1 hcle

end Work.Peluse.Prop36SW
