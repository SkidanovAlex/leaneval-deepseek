import Mathlib

namespace Work.LinnikAreas

/-- Arithmetic ("eighth line") estimate: the factor
`N^(3/16) * (2+|T|)^(3/16) * (log (N*(2+|T|)) + 2)` is dominated by
`N^(1/4) * (1+|T|)^(1/4)` up to an absolute constant. -/
theorem eighth_line_arith :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (T : ℝ), 1 ≤ N →
      (N : ℝ) ^ ((3 : ℝ) / 16) * (2 + |T|) ^ ((3 : ℝ) / 16)
        * (Real.log ((N : ℝ) * (2 + |T|)) + 2)
      ≤ C * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |T|) ^ ((1 : ℝ) / 4) := by
  refine ⟨18 * 2 ^ ((1 : ℝ) / 4), ?_, ?_⟩
  · positivity
  · intro N T hN
    set x : ℝ := (N : ℝ) with hx
    set y : ℝ := 2 + |T| with hy
    have hx1 : 1 ≤ x := by rw [hx]; exact_mod_cast hN
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hylow : 2 ≤ y := by rw [hy]; have := abs_nonneg T; linarith
    have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hylow
    have hz1 : 1 ≤ x * y := by
      have := mul_le_mul hx1 (show (1:ℝ) ≤ y by linarith) (by norm_num) hxpos.le
      simpa using this
    have hzpos : 0 < x * y := mul_pos hxpos hypos
    -- logarithm bound: `log z + 2 ≤ 18 * z^(1/16)` for `z ≥ 1`
    have hlog : Real.log (x * y) + 2 ≤ 18 * (x * y) ^ ((1:ℝ)/16) := by
      have hz16pos : 0 < (x*y) ^ ((1:ℝ)/16) := Real.rpow_pos_of_pos hzpos _
      have hsub := Real.log_le_sub_one_of_pos hz16pos
      rw [Real.log_rpow hzpos ((1:ℝ)/16)] at hsub
      have ht1 : (1:ℝ) ≤ (x*y) ^ ((1:ℝ)/16) := Real.one_le_rpow hz1 (by norm_num)
      nlinarith [hsub, ht1]
    have hx3 : 0 ≤ x ^ ((3:ℝ)/16) := Real.rpow_nonneg hxpos.le _
    have hy3 : 0 ≤ y ^ ((3:ℝ)/16) := Real.rpow_nonneg hypos.le _
    have hA : x^((3:ℝ)/16) * y^((3:ℝ)/16) = (x*y)^((3:ℝ)/16) := by
      rw [Real.mul_rpow hxpos.le hypos.le]
    have hB : (x*y)^((3:ℝ)/16) * (x*y)^((1:ℝ)/16) = (x*y)^((1:ℝ)/4) := by
      rw [← Real.rpow_add hzpos]
      rw [show (3:ℝ)/16 + (1:ℝ)/16 = (1:ℝ)/4 by norm_num]
    have hC : (x*y)^((1:ℝ)/4) = x^((1:ℝ)/4) * y^((1:ℝ)/4) := by
      rw [Real.mul_rpow hxpos.le hypos.le]
    have key : x^((3:ℝ)/16) * y^((3:ℝ)/16) * (x*y)^((1:ℝ)/16)
        = x^((1:ℝ)/4) * y^((1:ℝ)/4) := by
      rw [hA, hB, hC]
    have hy_le : y ≤ 2 * (1 + |T|) := by rw [hy]; have := abs_nonneg T; linarith
    have h1T : (0:ℝ) ≤ 1 + |T| := by positivity
    have hyquarter : y^((1:ℝ)/4) ≤ 2^((1:ℝ)/4) * (1+|T|)^((1:ℝ)/4) := by
      have h := Real.rpow_le_rpow hypos.le hy_le (by norm_num : (0:ℝ) ≤ (1:ℝ)/4)
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) h1T] at h
      exact h
    calc
      x^((3:ℝ)/16) * y^((3:ℝ)/16) * (Real.log (x*y) + 2)
          ≤ x^((3:ℝ)/16) * y^((3:ℝ)/16) * (18 * (x*y)^((1:ℝ)/16)) := by
            apply mul_le_mul_of_nonneg_left hlog
            exact mul_nonneg hx3 hy3
      _ = 18 * (x^((3:ℝ)/16) * y^((3:ℝ)/16) * (x*y)^((1:ℝ)/16)) := by ring
      _ = 18 * (x^((1:ℝ)/4) * y^((1:ℝ)/4)) := by rw [key]
      _ ≤ 18 * (x^((1:ℝ)/4) * (2^((1:ℝ)/4) * (1+|T|)^((1:ℝ)/4))) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 18)
            exact mul_le_mul_of_nonneg_left hyquarter (Real.rpow_nonneg hxpos.le _)
      _ = (18 * 2^((1:ℝ)/4)) * x^((1:ℝ)/4) * (1+|T|)^((1:ℝ)/4) := by ring

end Work.LinnikAreas
