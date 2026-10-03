import Mathlib

/-!
# The sharp maximum of `t ↦ t ^ a * exp (-(b * t))`

For `a, b, t > 0` we have
`t ^ a * exp (-(b * t)) ≤ (a / (b * exp 1)) ^ a`,
the value of the function `t ↦ t ^ a * exp (-(b * t))` at its maximum `t = a / b`.

The proof passes to logarithms: after writing both sides as exponentials the claim reduces to
`log (b * t / a) ≤ b * t / a - 1` (`Real.log_le_sub_one_of_pos`), i.e. `log x ≤ x - 1`.
-/

namespace Work.FIArea6Hecke.R.MGGrow

theorem rpow_mul_exp_neg_le {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    t ^ a * Real.exp (-(b * t)) ≤ (a / (b * Real.exp 1)) ^ a := by
  have hbt : 0 < b * t := mul_pos hb ht
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hA : 0 < a / (b * Real.exp 1) := div_pos ha (mul_pos hb he)
  rw [Real.rpow_def_of_pos ht, Real.rpow_def_of_pos hA, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hx : 0 < b * t / a := div_pos hbt ha
  have hlog := Real.log_le_sub_one_of_pos hx
  have hlogba : Real.log (b * t / a) = Real.log b + Real.log t - Real.log a := by
    rw [Real.log_div (ne_of_gt hbt) (ne_of_gt ha), Real.log_mul (ne_of_gt hb) (ne_of_gt ht)]
  have hlogA : Real.log (a / (b * Real.exp 1)) = Real.log a - Real.log b - 1 := by
    rw [Real.log_div (ne_of_gt ha) (ne_of_gt (mul_pos hb he)),
        Real.log_mul (ne_of_gt hb) (ne_of_gt he), Real.log_exp]
    ring
  rw [hlogA]
  have hmul := mul_le_mul_of_nonneg_left hlog ha.le
  rw [hlogba] at hmul
  have hsimp : a * (b * t / a - 1) = b * t - a := by
    field_simp
  nlinarith [hmul, hsimp]

end Work.FIArea6Hecke.R.MGGrow
