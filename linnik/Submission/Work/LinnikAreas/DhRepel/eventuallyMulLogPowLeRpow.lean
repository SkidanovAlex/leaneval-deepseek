import Mathlib

namespace Work.LinnikAreas.DhRepel

/-- For any constants `C > 0`, `A > 0` and natural number `k`, the polynomial
expression `C * (log x) ^ k` is eventually dominated by the power `x ^ A`.

This is the standard subordination of a power of `log` by a positive power: the
key input is `isLittleO_log_rpow_rpow_atTop`, which states that
`(log x) ^ r = o(x ^ s)` for every `s > 0` (and every real `r`); taking
`s = A / 2` and multiplying through by `C` gives, for large `x`,
`C * (log x) ^ k ≤ x ^ (A/2) ≤ x ^ A`. -/
theorem eventuallyMulLogPowLeRpow (C A : ℝ) (k : ℕ) (hC : 0 < C) (hA : 0 < A) :
    ∀ᶠ x : ℝ in Filter.atTop,
      C * (Real.log x) ^ k ≤ x ^ A := by
  have hA2 : 0 < A / 2 := by linarith
  -- `(log ·)^k` is little-o of `x^(A/2)` at `+∞`.
  have hlittle : (fun x : ℝ => Real.log x ^ (k : ℝ)) =o[Filter.atTop]
      fun x : ℝ => x ^ (A / 2) := isLittleO_log_rpow_rpow_atTop (k : ℝ) hA2
  -- Unfold the little-o bound with constant `1 / C`.
  have hbound := hlittle.bound (show (0 : ℝ) < 1 / C by positivity)
  filter_upwards [hbound, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  -- for `x ≥ 1` the norms are the values themselves, and the real power
  -- `(log x)^↑k` is the natural power `(log x)^k`.
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) (k : ℝ)),
      Real.norm_of_nonneg (Real.rpow_nonneg (le_trans zero_le_one hx1) (A / 2))] at hx
  rw [Real.rpow_natCast] at hx
  have hmul : C * (Real.log x) ^ k ≤ C * ((1 / C) * x ^ (A / 2)) :=
    mul_le_mul_of_nonneg_left hx (le_of_lt hC)
  have hsimp : C * ((1 / C) * x ^ (A / 2)) = x ^ (A / 2) := by field_simp
  have hmono : x ^ (A / 2) ≤ x ^ A := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  calc C * (Real.log x) ^ k ≤ C * ((1 / C) * x ^ (A / 2)) := hmul
    _ = x ^ (A / 2) := hsimp
    _ ≤ x ^ A := hmono

end Work.LinnikAreas.DhRepel
