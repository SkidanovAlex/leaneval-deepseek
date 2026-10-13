import Mathlib.Analysis.Complex.Exponential
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.Traces

open scoped Real Topology

/-- The elementary inequality behind `wtZ_shift_mul_le`: for `|p| ≤ ε` and `z > 0`,
`1 + z ≤ e^{3(ε+p)/4}(1 + z e^{-p})`.

Writing `ε - b := 3(ε+p)/4` (so that `b = (3ε-p)/4 ∈ [0,ε]`, since `|p| ≤ ε`), the right hand
side is `e^{3(ε-b)} + z e^{b}` and both exponentials are `≥ 1`. -/
theorem one_add_le_exp_mul (z p ε : ℝ) (hz : 0 < z) (hε : 0 ≤ ε) (hp : |p| ≤ ε) :
    1 + z ≤ Real.exp (3 * (ε + p) / 4) * (1 + z * Real.exp (-p)) := by
  have hp1 : -ε ≤ p := (abs_le.mp hp).1
  have hp2 : p ≤ ε := (abs_le.mp hp).2
  have ht1 : (0 : ℝ) ≤ 3 * (ε + p) / 4 := by linarith
  have ht2 : (0 : ℝ) ≤ 3 * (ε + p) / 4 - p := by linarith
  have hA : 1 ≤ Real.exp (3 * (ε + p) / 4) := Real.one_le_exp ht1
  have hB : 1 ≤ Real.exp (3 * (ε + p) / 4 - p) := Real.one_le_exp ht2
  have hsplit : Real.exp (3 * (ε + p) / 4) * (1 + z * Real.exp (-p))
      = Real.exp (3 * (ε + p) / 4) + z * Real.exp (3 * (ε + p) / 4 - p) := by
    have h : Real.exp (3 * (ε + p) / 4) * Real.exp (-p) = Real.exp (3 * (ε + p) / 4 - p) := by
      rw [← Real.exp_add]
      congr 1
    calc Real.exp (3 * (ε + p) / 4) * (1 + z * Real.exp (-p))
        = Real.exp (3 * (ε + p) / 4) * 1
            + Real.exp (3 * (ε + p) / 4) * (z * Real.exp (-p)) := by rw [mul_add]
      _ = Real.exp (3 * (ε + p) / 4)
            + z * (Real.exp (3 * (ε + p) / 4) * Real.exp (-p)) := by ring
      _ = Real.exp (3 * (ε + p) / 4) + z * Real.exp (3 * (ε + p) / 4 - p) := by rw [h]
  rw [hsplit]
  refine add_le_add hA ?_
  have h := mul_le_mul_of_nonneg_left hB hz.le
  simpa using h

/-- The key inequality: for `|p| ≤ ε`, `z > 0`,
`(1 + z)^4 e^{-3p} ≤ e^{3ε} (1 + z e^{-p})^4`. -/
theorem pow_four_key (z p ε : ℝ) (hz : 0 < z) (hε : 0 ≤ ε) (hp : |p| ≤ ε) :
    (1 + z) ^ 4 * Real.exp (-p) ^ 3
      ≤ Real.exp (3 * ε) * (1 + z * Real.exp (-p)) ^ 4 := by
  have hheart := one_add_le_exp_mul z p ε hz hε hp
  have hexp_pow : (Real.exp (3 * (ε + p) / 4)) ^ 4 = Real.exp (3 * (ε + p)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h4 : (1 + z) ^ 4 ≤ Real.exp (3 * (ε + p)) * (1 + z * Real.exp (-p)) ^ 4 := by
    calc (1 + z) ^ 4
        ≤ (Real.exp (3 * (ε + p) / 4) * (1 + z * Real.exp (-p))) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hheart 4
      _ = (Real.exp (3 * (ε + p) / 4)) ^ 4 * (1 + z * Real.exp (-p)) ^ 4 := by rw [mul_pow]
      _ = Real.exp (3 * (ε + p)) * (1 + z * Real.exp (-p)) ^ 4 := by rw [hexp_pow]
  have hprod : Real.exp (3 * p) * Real.exp (-p) ^ 3 = 1 := by
    have h3 : Real.exp (-p) ^ 3 = Real.exp (-p + -p + -p) := by
      rw [show Real.exp (-p) ^ 3 = Real.exp (-p) * Real.exp (-p) * Real.exp (-p) by ring,
        ← Real.exp_add]
      rw [← Real.exp_add]
    rw [h3, ← Real.exp_add]
    rw [show 3 * p + (-p + -p + -p) = 0 by ring, Real.exp_zero]
  have h6 : Real.exp (3 * (ε + p)) * Real.exp (-p) ^ 3 = Real.exp (3 * ε) := by
    rw [show Real.exp (3 * (ε + p)) = Real.exp (3 * ε) * Real.exp (3 * p) by
          rw [← Real.exp_add]; congr 1; ring]
    rw [show Real.exp (3 * ε) * Real.exp (3 * p) * Real.exp (-p) ^ 3
          = Real.exp (3 * ε) * (Real.exp (3 * p) * Real.exp (-p) ^ 3) by ring, hprod, mul_one]
  have h5 := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ Real.exp (-p) ^ 3)
  calc (1 + z) ^ 4 * Real.exp (-p) ^ 3
      ≤ (Real.exp (3 * (ε + p)) * (1 + z * Real.exp (-p)) ^ 4) * Real.exp (-p) ^ 3 := h5
    _ = Real.exp (3 * ε) * (1 + z * Real.exp (-p)) ^ 4 := by
        rw [show (Real.exp (3 * (ε + p)) * (1 + z * Real.exp (-p)) ^ 4) * Real.exp (-p) ^ 3
              = (Real.exp (3 * (ε + p)) * Real.exp (-p) ^ 3)
                  * (1 + z * Real.exp (-p)) ^ 4 by ring, h6]

theorem wtZ_shift_mul_le (z p ε : ℝ) (hz : 0 < z) (hε : 0 ≤ ε) (hp : |p| ≤ ε) :
    z * Work.Spaces.w z ^ 2
      ≤ Real.exp (3 * ε) * (Work.FTS.StrongEps.zShift z p
          * Work.Spaces.w (Work.FTS.StrongEps.zShift z p) ^ 2) := by
  have hkey := pow_four_key z p ε hz hε hp
  have hL : z * Work.Spaces.w z ^ 2 = (1 + z) ^ 4 / z ^ 3 := by
    change z * ((1 + z) ^ 2 / z ^ 2) ^ 2 = (1 + z) ^ 4 / z ^ 3
    field_simp
  have hR : Work.FTS.StrongEps.zShift z p * Work.Spaces.w (Work.FTS.StrongEps.zShift z p) ^ 2
      = (1 + z * Real.exp (-p)) ^ 4 / (z ^ 3 * Real.exp (-p) ^ 3) := by
    change z * Real.exp (-p) * ((1 + z * Real.exp (-p)) ^ 2 / (z * Real.exp (-p)) ^ 2) ^ 2
        = (1 + z * Real.exp (-p)) ^ 4 / (z ^ 3 * Real.exp (-p) ^ 3)
    field_simp
  rw [hL, hR, ← mul_div_assoc]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 3)
        (by positivity : (0 : ℝ) < z ^ 3 * Real.exp (-p) ^ 3)]
  have h7 := mul_le_mul_of_nonneg_right hkey (by positivity : (0 : ℝ) ≤ z ^ 3)
  rw [show (1 + z) ^ 4 * (z ^ 3 * Real.exp (-p) ^ 3)
        = (1 + z) ^ 4 * Real.exp (-p) ^ 3 * z ^ 3 by ring]
  exact h7

end Work.FTS.StrongEps.Traces
