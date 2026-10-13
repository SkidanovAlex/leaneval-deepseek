import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS_EllLimOK.PkgJets.CosTailDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

/-!
# The reflected comparison function dominates `ctG` on `(0, π/4]`

`ctG w = sin(2w)^{-η}/sin(w)^4` and `ctB w = (4/π)^{-η}(π/2)^4 w^{-(4+η)}`, `η = 99/100`.
Since `sin(t) ≥ (2/π)t` on `[0, π/2]`, we have `sin w ≥ (2/π)w` (so `1/sin(w)^4 ≤ (π/2)^4 w^{-4}`)
and `sin(2w) ≥ (4/π)w` (so `sin(2w)^{-η} ≤ (4/π)^{-η} w^{-η}`).  Multiplying the two bounds
gives `ctG w ≤ (4/π)^{-η}(π/2)^4 w^{-4}w^{-η} = ctB w` for `w > 0`.  Note the endpoint
`w = π/4` is admissible: there `ctG = 4`, `ctB = 16`.
-/

theorem ctG_le_ctB :
    ∀ w : ℝ, w ∈ Set.Ioc 0 (Real.pi / 4) → ctG w ≤ ctB w := by
  intro w hw
  obtain ⟨hw0, hw4⟩ := hw
  -- `sin (2w) ≥ (4/π) w`
  have hsin1 : 4 / Real.pi * w ≤ Real.sin (2 * w) := by
    have h := Real.mul_le_sin (x := 2 * w) (by linarith [Real.pi_pos] : (0 : ℝ) ≤ 2 * w)
      (by linarith [Real.pi_pos] : 2 * w ≤ Real.pi / 2)
    have heq : 2 / Real.pi * (2 * w) = 4 / Real.pi * w := by ring
    rwa [heq] at h
  -- `sin w ≥ (2/π) w`
  have hsin2 : 2 / Real.pi * w ≤ Real.sin w :=
    Real.mul_le_sin hw0.le (by linarith [Real.pi_pos])
  have hpos1 : 0 < 4 / Real.pi * w := by positivity
  have hpos2 : 0 < 2 / Real.pi * w := by positivity
  have hs1 : 0 < Real.sin w := lt_of_lt_of_le hpos2 hsin2
  -- numerator bound
  have hnum : (Real.sin (2 * w)) ^ (-(99 / 100 : ℝ))
      ≤ (4 / Real.pi) ^ (-(99 / 100 : ℝ)) * w ^ (-(99 / 100 : ℝ)) := by
    calc (Real.sin (2 * w)) ^ (-(99 / 100 : ℝ))
        ≤ (4 / Real.pi * w) ^ (-(99 / 100 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hpos1 hsin1 (by norm_num)
      _ = (4 / Real.pi) ^ (-(99 / 100 : ℝ)) * w ^ (-(99 / 100 : ℝ)) :=
          Real.mul_rpow (by positivity) hw0.le
  -- denominator bound `((2/π)w)^4 ≤ sin(w)^4`
  have hsinw : (2 / Real.pi) ^ (4 : ℕ) * w ^ (4 : ℕ) ≤ (Real.sin w) ^ (4 : ℕ) := by
    have h := pow_le_pow_left₀ hpos2.le hsin2 4
    rwa [mul_pow] at h
  have hprod : (Real.pi / 2) ^ (4 : ℕ) * (2 / Real.pi) ^ (4 : ℕ) = 1 := by
    rw [← mul_pow]
    have h : Real.pi / 2 * (2 / Real.pi) = 1 := by field_simp
    rw [h]; norm_num
  have hwpow : w ^ (-(4 + 99 / 100 : ℝ)) * w ^ (4 : ℕ) = w ^ (-(99 / 100 : ℝ)) := by
    rw [← Real.rpow_natCast w 4, ← Real.rpow_add hw0]
    norm_num
  -- `w^{-η} ≤ (π/2)^4 w^{-(4+η)} sin(w)^4`
  have hkey : w ^ (-(99 / 100 : ℝ))
      ≤ (Real.pi / 2) ^ (4 : ℕ) * w ^ (-(4 + 99 / 100 : ℝ)) * (Real.sin w) ^ (4 : ℕ) := by
    have hstep : (Real.pi / 2) ^ (4 : ℕ) * w ^ (-(4 + 99 / 100 : ℝ))
          * ((2 / Real.pi) ^ (4 : ℕ) * w ^ (4 : ℕ))
        ≤ (Real.pi / 2) ^ (4 : ℕ) * w ^ (-(4 + 99 / 100 : ℝ)) * (Real.sin w) ^ (4 : ℕ) :=
      mul_le_mul_of_nonneg_left hsinw (by positivity)
    have heq : (Real.pi / 2) ^ (4 : ℕ) * w ^ (-(4 + 99 / 100 : ℝ))
          * ((2 / Real.pi) ^ (4 : ℕ) * w ^ (4 : ℕ))
        = w ^ (-(99 / 100 : ℝ)) := by
      calc (Real.pi / 2) ^ (4 : ℕ) * w ^ (-(4 + 99 / 100 : ℝ))
            * ((2 / Real.pi) ^ (4 : ℕ) * w ^ (4 : ℕ))
          = ((Real.pi / 2) ^ (4 : ℕ) * (2 / Real.pi) ^ (4 : ℕ))
              * (w ^ (-(4 + 99 / 100 : ℝ)) * w ^ (4 : ℕ)) := by ring
        _ = 1 * w ^ (-(99 / 100 : ℝ)) := by rw [hprod, hwpow]
        _ = w ^ (-(99 / 100 : ℝ)) := by ring
    rw [heq] at hstep
    exact hstep
  rw [ctG, ctB]
  rw [div_le_iff₀ (pow_pos hs1 4)]
  calc (Real.sin (2 * w)) ^ (-(99 / 100 : ℝ))
      ≤ (4 / Real.pi) ^ (-(99 / 100 : ℝ)) * w ^ (-(99 / 100 : ℝ)) := hnum
    _ ≤ (4 / Real.pi) ^ (-(99 / 100 : ℝ))
          * ((Real.pi / 2) ^ (4 : ℕ) * w ^ (-(4 + 99 / 100 : ℝ)) * (Real.sin w) ^ (4 : ℕ)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (4 / Real.pi) ^ (-(99 / 100 : ℝ)) * (Real.pi / 2) ^ (4 : ℕ) * w ^ (-(4 + 99 / 100 : ℝ))
          * (Real.sin w) ^ (4 : ℕ) := by ring

end Work.FTS_EllLimOK.PkgJets
