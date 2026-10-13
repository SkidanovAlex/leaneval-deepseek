import Mathlib

namespace Work.WilE2

theorem sum_ofReal_grid {n N : ℕ} (c : ℝ) (hc : 0 ≤ c) :
    (∑ v : Fin n → Fin N, ENNReal.ofReal c) = ENNReal.ofReal ((N : ℝ) ^ n * c) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun]
  simp only [Fintype.card_fin]
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, Nat.cast_pow,
    ENNReal.ofReal_pow (Nat.cast_nonneg N)]
  rw [ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg N) n)]
  rw [ENNReal.ofReal_pow (Nat.cast_nonneg N)]

end Work.WilE2
