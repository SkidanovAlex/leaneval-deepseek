import Mathlib

namespace Work.ZeroDensity.Huxley

/-- If `x^δ ≥ 2` (in particular for `x ≥ 2^{1/δ}`), then `a + 1 ≤ x^{δa}` for all `a`.
Proof idea: `x^{δa} = (x^δ)^a ≥ 2^a ≥ a + 1` (`Nat.lt_two_pow_self`), and `a = 0` is `1 ≤ 1`. -/
lemma succ_le_rpow_of_two_le_rpow {δ : ℝ} (x a : ℕ) (hx : 2 ≤ x)
    (h : 2 ≤ (x : ℝ) ^ δ) : (a : ℝ) + 1 ≤ (x : ℝ) ^ ((a : ℝ) * δ) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hx0' : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hx0
  -- `(x^δ)^a ≥ 2^a`
  have step1 : (2 : ℝ) ^ ((a : ℝ)) ≤ ((x : ℝ) ^ δ) ^ ((a : ℝ)) :=
    Real.rpow_le_rpow (by norm_num) h (by positivity)
  have step2 : ((x : ℝ) ^ δ) ^ ((a : ℝ)) = (x : ℝ) ^ (δ * (a : ℝ)) :=
    (Real.rpow_mul hx0' δ (a : ℝ)).symm
  -- `a + 1 ≤ 2^a`
  have hle : a + 1 ≤ 2 ^ a := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := a))
  have step4 : ((a : ℝ) + 1) ≤ (2 : ℝ) ^ a := by
    have := (Nat.cast_le (α := ℝ)).mpr hle
    push_cast at this
    simpa using this
  calc (a : ℝ) + 1 ≤ (2 : ℝ) ^ a := step4
    _ = (2 : ℝ) ^ ((a : ℝ)) := by rw [Real.rpow_natCast]
    _ ≤ ((x : ℝ) ^ δ) ^ ((a : ℝ)) := step1
    _ = (x : ℝ) ^ (δ * (a : ℝ)) := step2
    _ = (x : ℝ) ^ ((a : ℝ) * δ) := by rw [mul_comm]

end Work.ZeroDensity.Huxley
