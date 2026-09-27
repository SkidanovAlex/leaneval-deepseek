import Mathlib

namespace Work.KT.D2

theorem TrigAux {x : ℝ} (h0 : 0 < x) (h1 : x < Real.pi / 2) :
    1 - Real.cos x < Real.sin x := by
  -- For `x` in `(0, π/2)`, both `sin x` and `cos x` are strictly positive.
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
  -- Hence `(sin x + cos x)^2 = 1 + 2 sin x cos x > 1`.
  have hprod : 0 < Real.sin x * Real.cos x := mul_pos hsin hcos
  have hsq : (Real.sin x + Real.cos x) ^ 2 = 1 + 2 * (Real.sin x * Real.cos x) := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hgt : (1 : ℝ) ^ 2 < (Real.sin x + Real.cos x) ^ 2 := by
    rw [hsq]; norm_num; linarith
  -- Since `sin x + cos x > 0`, squaring is injective on the positive side.
  have habs : |(1 : ℝ)| < |Real.sin x + Real.cos x| := sq_lt_sq.mp hgt
  have hsum_pos : 0 < Real.sin x + Real.cos x := by linarith
  rw [abs_one, abs_of_pos hsum_pos] at habs
  -- `1 < sin x + cos x` is exactly `1 - cos x < sin x`.
  linarith

end Work.KT.D2
