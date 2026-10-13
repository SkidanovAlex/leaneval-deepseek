import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Elliptic.Gbar_hardy_lintegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open MeasureTheory Set

theorem Gbar_hardy_lintegral_ofReal (β : ℝ) (hβ : 1 < β) (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) :
    (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2))
      ≤ ENNReal.ofReal (4 / (β * (3 * β - 2)) * ∫ z in Set.Ioi (0 : ℝ), f z ^ 2) := by
  have hb0 : (0 : ℝ) < β := by linarith
  have hb2 : (0 : ℝ) < 3 * β - 2 := by linarith
  have hJ : (0 : ℝ) ≤ ∫ z in Set.Ioi (0 : ℝ), f z ^ 2 :=
    integral_nonneg (fun z => sq_nonneg (f z))
  -- Pointwise (weighted Cauchy--Schwarz) bound, at the level of `ℝ≥0∞`.
  have hpoint : ∀ z ∈ Set.Ioi (0 : ℝ),
      ENNReal.ofReal ((z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2)
        ≤ ENNReal.ofReal (2 / β) * (ENNReal.ofReal (z ^ (-(3 * β / 2))) *
            (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2))) := by
    intro z hz
    have hzpos : 0 < z := hz
    have hrz : (z ^ (-β)) ^ 2 = z ^ (-(2 * β)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
      congr 1
      ring
    have hc3 : z ^ (-(2 * β)) * z ^ (β / 2) = z ^ (-(3 * β / 2)) := by
      rw [← Real.rpow_add hzpos]
      congr 1
      ring
    have hp := hardy_op_L2_pointwise β hβ f hf hzpos
    have hle : (z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2
        ≤ (2 / β) * z ^ (-(3 * β / 2)) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal := by
      rw [mul_pow, hrz]
      calc z ^ (-(2 * β)) * (∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2
          ≤ z ^ (-(2 * β)) * ((2 * z ^ (β / 2) / β) *
              (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal) :=
            mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hzpos.le _)
        _ = (2 / β) * z ^ (-(3 * β / 2)) *
              (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal := by
            rw [← hc3]; ring
    refine (ENNReal.ofReal_le_ofReal hle).trans ?_
    rw [show (2 / β) * z ^ (-(3 * β / 2)) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal
        = (2 / β) * (z ^ (-(3 * β / 2)) *
            (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal) by ring]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Real.rpow_nonneg hzpos.le _)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ENNReal.ofReal_toReal_le (bot_le)) (bot_le)
  -- Integrate the pointwise bound and pull out the constant `2/β`.
  have hstep : (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2))
      ≤ ENNReal.ofReal (2 / β) *
        (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (z ^ (-(3 * β / 2))) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2))) := by
    rw [← lintegral_const_mul' (ENNReal.ofReal (2 / β)) _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' measurableSet_Ioi hpoint
  have hT := hardy_op_L2_tonelli β hβ f hf
  rw [hT] at hstep
  refine hstep.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 / β)]
  congr 1
  have hb0ne : β ≠ 0 := ne_of_gt hb0
  have hb2ne : 3 * β - 2 ≠ 0 := ne_of_gt hb2
  field_simp
  ring

end Work.Elliptic
