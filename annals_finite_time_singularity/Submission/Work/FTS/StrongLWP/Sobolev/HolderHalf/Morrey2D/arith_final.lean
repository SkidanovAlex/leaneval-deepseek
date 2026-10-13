import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D

/-- Auxiliary: `(4 a ^ 2) ^ (3/4) * sqrt a = 2 * sqrt 2 * a ^ 2` for `a > 0`. -/
private lemma rpow_four_sq_mul_sqrt {a : ℝ} (ha : 0 < a) :
    (4 * a ^ 2) ^ (3 / 4 : ℝ) * Real.sqrt a = 2 * Real.sqrt 2 * a ^ 2 := by
  have hsplit : (4 * a ^ 2) ^ (3 / 4 : ℝ) = 4 ^ ((3 : ℝ) / 4) * a ^ ((3 : ℝ) / 2) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity : (0 : ℝ) ≤ a ^ 2)]
    congr 1
    rw [← Real.rpow_natCast a 2, ← Real.rpow_mul (le_of_lt ha)]
    norm_num
  have h4 : (4 : ℝ) ^ ((3 : ℝ) / 4) = 2 * Real.sqrt 2 := by
    have h2 : ((2 : ℝ) ^ (2 : ℝ)) = 4 := by norm_num [Real.rpow_natCast]
    calc (4 : ℝ) ^ ((3 : ℝ) / 4) = ((2 : ℝ) ^ (2 : ℝ)) ^ ((3 : ℝ) / 4) := by rw [h2]
      _ = (2 : ℝ) ^ ((2 : ℝ) * ((3 : ℝ) / 4)) := by
            rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (2 : ℝ) ^ ((3 : ℝ) / 2) := by
            rw [show (2 : ℝ) * ((3 : ℝ) / 4) = (3 : ℝ) / 2 by norm_num]
      _ = (2 : ℝ) ^ ((1 : ℝ) + 1 / 2) := by
            rw [show (3 : ℝ) / 2 = (1 : ℝ) + 1 / 2 by norm_num]
      _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ ((1 : ℝ) / 2) := by
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = 2 * Real.sqrt 2 := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  calc (4 * a ^ 2) ^ (3 / 4 : ℝ) * Real.sqrt a
      = (4 ^ ((3 : ℝ) / 4) * a ^ ((3 : ℝ) / 2)) * Real.sqrt a := by rw [hsplit]
    _ = (2 * Real.sqrt 2 * a ^ ((3 : ℝ) / 2)) * Real.sqrt a := by rw [h4]
    _ = 2 * Real.sqrt 2 * (a ^ ((3 : ℝ) / 2) * Real.sqrt a) := by ring
    _ = 2 * Real.sqrt 2 * (a ^ ((3 : ℝ) / 2) * a ^ ((1 : ℝ) / 2)) := by
          rw [Real.sqrt_eq_rpow a]
    _ = 2 * Real.sqrt 2 * a ^ ((3 : ℝ) / 2 + 1 / 2) := by rw [← Real.rpow_add ha]
    _ = 2 * Real.sqrt 2 * a ^ (2 : ℕ) := by
          rw [show (3 : ℝ) / 2 + 1 / 2 = 2 by norm_num]
          norm_num [Real.rpow_natCast]

theorem arith_final {a d I : ℝ} (ha : 0 < a) :
    (1 / (4 * a ^ 2)) * ((a + d) * (2 * (4 * a ^ 2) ^ (3 / 4 : ℝ) * I))
      = Real.sqrt 2 * I * ((a + d) / Real.sqrt a) := by
  have hXa : (4 * a ^ 2) ^ (3 / 4 : ℝ) = 2 * Real.sqrt 2 * a ^ 2 / Real.sqrt a := by
    rw [eq_div_iff (ne_of_gt (Real.sqrt_pos.mpr ha))]
    exact rpow_four_sq_mul_sqrt ha
  rw [hXa]
  field_simp
  ring

end Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D
