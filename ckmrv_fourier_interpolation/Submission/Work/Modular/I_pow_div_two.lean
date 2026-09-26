import Mathlib

namespace Work.Modular

/-- `Complex.I ^ (n / 2) = 1` when `8 ∣ n`: then `n / 2` is a multiple of `4`. -/
lemma I_pow_div_two {n : ℕ} (hn : 8 ∣ n) : Complex.I ^ (n / 2) = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h : (8 * k) / 2 = 4 * k := by omega
  rw [h, pow_mul, Complex.I_pow_four, one_pow]

end Work.Modular
