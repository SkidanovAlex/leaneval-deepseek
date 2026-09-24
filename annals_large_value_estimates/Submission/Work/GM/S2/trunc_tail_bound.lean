import Mathlib

/-!
# Bounding a truncated tail: `a^j / (N^j Y^{j-1}) ≤ A / (N T^{η(j-1)})`

With `Y = A T^η / N`, the two sides are equal after clearing constants: indeed
`N^{j-1} Y^{j-1} = (N Y)^{j-1} = (A T^η)^{j-1} = A^{j-1} T^{η(j-1)}`, so
`A / (N T^{η(j-1)}) = A^j / (N^j Y^{j-1})`, and the claim reduces to `a^j ≤ A^j`
from `0 ≤ a ≤ A`.  This is the utility used in §6 (the `k = 4` truncation of the
tail of the Dirichlet polynomial).
-/

namespace Work.GM.S2

theorem trunc_tail_bound {a A N T η Y : ℝ} {j : ℕ} (hj : 2 ≤ j) (ha : 0 ≤ a) (hAa : a ≤ A)
    (hA : 0 < A) (hN : 0 < N) (hT : 1 ≤ T) (hY : Y = A * T ^ η / N) :
    a ^ j / (N ^ j * Y ^ (j - 1)) ≤ A / (N * T ^ (η * ((j : ℝ) - 1))) := by
  -- `T > 0`, so `T^η > 0` and `Y > 0`.
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT
  -- Write `j = k + 1` (`k = j - 1`), so all exponents become natural numbers.
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 :=
    ⟨j - 1, (Nat.succ_pred_eq_of_pos (by omega : 0 < j)).symm⟩
  -- `(j : ℝ) - 1 = (k : ℝ)`.
  have hexp : η * (((k + 1 : ℕ) : ℝ) - 1) = η * (k : ℝ) := by push_cast; ring
  have hYpow : Y ^ ((k + 1) - 1) = Y ^ k := by rw [Nat.add_sub_cancel]
  rw [hexp, hYpow]
  -- `(T^η)^k = T^{η k}`.
  have hTηk : (T ^ η) ^ k = T ^ (η * (k : ℝ)) := by
    rw [← Real.rpow_natCast (T ^ η) k, ← Real.rpow_mul (le_of_lt hTpos) η (k : ℝ)]
  have hYk : Y ^ k = A ^ k * (T ^ η) ^ k / N ^ k := by
    rw [hY, div_pow, mul_pow]
  have hNk : N ^ k ≠ 0 := pow_ne_zero _ (ne_of_gt hN)
  -- The two denominators agree up to the constant factor `A^k`.
  have key : A * (N ^ (k + 1) * Y ^ k) = A ^ (k + 1) * (N * T ^ (η * (k : ℝ))) := by
    rw [hYk, hTηk, pow_succ N k, pow_succ A k]
    field_simp
  have hYpos : 0 < Y := by rw [hY]; positivity
  have hTηpos : 0 < T ^ η := Real.rpow_pos_of_pos hTpos η
  have hden1 : 0 < N ^ (k + 1) * Y ^ k := by positivity
  have hden2 : 0 < N * T ^ (η * (k : ℝ)) := by positivity
  rw [div_le_div_iff₀ hden1 hden2, key, mul_le_mul_iff_of_pos_right hden2]
  exact pow_le_pow_left₀ ha hAa (k + 1)

end Work.GM.S2
