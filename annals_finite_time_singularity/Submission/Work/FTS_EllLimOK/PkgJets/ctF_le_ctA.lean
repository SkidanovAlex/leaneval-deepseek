import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS_EllLimOK.PkgJets.CosTailDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

/-- On `(0, π/4]` the integrand `ctF` is dominated by `ctA`: Jordan's inequality gives
`sin(2s) ≥ (4/π) s` and `cos s ≥ 1/2` gives `cos s ^ 4 ≥ 1/16`. -/
theorem ctF_le_ctA :
    ∀ s : ℝ, s ∈ Set.Ioc 0 (Real.pi / 4) → ctF s ≤ ctA s := by
  intro s hs
  have hs0 : 0 < s := hs.1
  have hsle : s ≤ Real.pi / 4 := hs.2
  -- Jordan: `(4/π) s ≤ sin (2s)`
  have hsin_ge : (4 / Real.pi) * s ≤ Real.sin (2 * s) := by
    have h := Real.mul_le_sin (x := 2 * s) (by linarith) (by linarith [Real.pi_pos])
    have h' : 2 / Real.pi * (2 * s) = (4 / Real.pi) * s := by ring
    linarith [h, h']
  have hbase_pos : 0 < (4 / Real.pi) * s := by
    have : (0 : ℝ) < 4 / Real.pi := by positivity
    exact mul_pos this hs0
  have hsin_le : Real.sin (2 * s) ^ (-(99 / 100 : ℝ))
      ≤ ((4 / Real.pi) * s) ^ (-(99 / 100 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hbase_pos hsin_ge (by norm_num)
  have hmul : ((4 / Real.pi) * s) ^ (-(99 / 100 : ℝ))
      = (4 / Real.pi) ^ (-(99 / 100 : ℝ)) * s ^ (-(99 / 100 : ℝ)) :=
    Real.mul_rpow (by positivity) (le_of_lt hs0)
  -- `cos s ≥ 1/2`
  have hcos_ge : (1 : ℝ) / 2 ≤ Real.cos s := by
    have h1 := Real.cos_le_cos_of_nonneg_of_le_pi (x := s) (y := Real.pi / 4)
      (le_of_lt hs0) (by linarith [Real.pi_pos]) hsle
    rw [Real.cos_pi_div_four] at h1
    have h2 : (1 : ℝ) / 2 ≤ Real.sqrt 2 / 2 := by
      have h3 := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num)
      rw [Real.sqrt_one] at h3
      linarith
    linarith
  have hcos_pos : 0 < Real.cos s :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hcos_ge
  have hcos4_pos : 0 < (Real.cos s) ^ 4 := pow_pos hcos_pos 4
  have hcos4 : (1 : ℝ) / 16 ≤ (Real.cos s) ^ 4 := by
    have hc : ((1 : ℝ) / 2) ^ 4 = 1 / 16 := by norm_num
    rw [← hc]
    exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hcos_ge 4
  have hB_nonneg : 0 ≤ (4 / Real.pi) ^ (-(99 / 100 : ℝ)) * s ^ (-(99 / 100 : ℝ)) := by
    positivity
  unfold ctF ctA
  calc
    Real.sin (2 * s) ^ (-(99 / 100 : ℝ)) / (Real.cos s) ^ 4
        ≤ ((4 / Real.pi) * s) ^ (-(99 / 100 : ℝ)) / (Real.cos s) ^ 4 :=
          div_le_div_of_nonneg_right hsin_le hcos4_pos.le
    _ = ((4 / Real.pi) ^ (-(99 / 100 : ℝ)) * s ^ (-(99 / 100 : ℝ))) / (Real.cos s) ^ 4 := by
          rw [hmul]
    _ ≤ 16 * (4 / Real.pi) ^ (-(99 / 100 : ℝ)) * s ^ (-(99 / 100 : ℝ)) := by
          rw [div_le_iff₀ hcos4_pos]
          have h16 : 1 ≤ 16 * (Real.cos s) ^ 4 := by linarith
          calc (4 / Real.pi) ^ (-(99 / 100 : ℝ)) * s ^ (-(99 / 100 : ℝ))
              = ((4 / Real.pi) ^ (-(99 / 100 : ℝ)) * s ^ (-(99 / 100 : ℝ))) * 1 := by ring
            _ ≤ ((4 / Real.pi) ^ (-(99 / 100 : ℝ)) * s ^ (-(99 / 100 : ℝ)))
                  * (16 * (Real.cos s) ^ 4) :=
                  mul_le_mul_of_nonneg_left h16 hB_nonneg
            _ = (16 * (4 / Real.pi) ^ (-(99 / 100 : ℝ)) * s ^ (-(99 / 100 : ℝ)))
                  * (Real.cos s) ^ 4 := by ring

end Work.FTS_EllLimOK.PkgJets
