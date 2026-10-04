import Mathlib
import Submission.Work.Diff.C.model_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

/-- The closed form `modelW a u κ = -(modelD a u κ) / √(1 - (modelG a u κ)²)` of the derivative of
the model angle is differentiable at `0`, with derivative `cot a * (u ^ 2 - (u * κ) ^ 2)`. -/
theorem modelW_hasDerivAt_zero {a u κ : ℝ} (ha0 : 0 < a) (haπ : a < Real.pi) :
    HasDerivAt (modelW a u κ) (Real.cot a * (u ^ 2 - (u * κ) ^ 2)) 0 := by
  have hsin : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 haπ
  have hP0 : 1 - (modelG a u κ 0) ^ 2 = Real.sin a ^ 2 := by
    rw [modelG_zero, ← Real.sin_sq]
  have hP0pos : 0 < 1 - (modelG a u κ 0) ^ 2 := by
    rw [hP0]; positivity
  have hGd : HasDerivAt (modelG a u κ) (modelD a u κ 0) 0 := modelG_hasDerivAt a u κ 0
  -- derivative of `1 - modelG ^ 2`
  have hPd : HasDerivAt (fun s => 1 - (modelG a u κ s) ^ 2)
      (-(2 * modelG a u κ 0 * modelD a u κ 0)) 0 := by
    have h2 : HasDerivAt (fun s => (modelG a u κ s) ^ 2)
        (2 * (modelG a u κ 0) ^ (2 - 1) * modelD a u κ 0) 0 := hGd.pow 2
    have h1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 := hasDerivAt_const 0 1
    have h := h1.sub h2
    convert h using 1
    norm_num
  -- derivative of `√(1 - modelG ^ 2)`
  have hsqrt : HasDerivAt (fun s => Real.sqrt (1 - (modelG a u κ s) ^ 2))
      (-(u * κ * Real.cos a)) 0 := by
    have hval : (1 / (2 * Real.sqrt (1 - (modelG a u κ 0) ^ 2))
        * (-(2 * (modelG a u κ 0) * modelD a u κ 0))) = -(u * κ * Real.cos a) := by
      rw [modelG_zero, modelD_zero, ← Real.sin_sq, Real.sqrt_sq (le_of_lt hsin)]
      field_simp
    have h := (Real.hasDerivAt_sqrt (ne_of_gt hP0pos)).comp 0 hPd
    rw [hval] at h
    exact h
  -- derivative of the numerator `-modelD`
  have hf : HasDerivAt (fun s => -(modelD a u κ s)) (u ^ 2 * Real.cos a) 0 := by
    have h := (modelD_hasDerivAt_zero a u κ).neg
    convert h using 1
    ring
  have hdiv := hf.div hsqrt (ne_of_gt (Real.sqrt_pos_of_pos hP0pos))
  have hval2 : (u ^ 2 * Real.cos a * Real.sqrt (1 - (modelG a u κ 0) ^ 2)
      - (-(modelD a u κ 0)) * (-(u * κ * Real.cos a)))
      / (Real.sqrt (1 - (modelG a u κ 0) ^ 2)) ^ 2
      = Real.cot a * (u ^ 2 - (u * κ) ^ 2) := by
    rw [modelG_zero, modelD_zero, ← Real.sin_sq, Real.sqrt_sq (le_of_lt hsin),
      Real.cot_eq_cos_div_sin]
    field_simp
  rw [hval2] at hdiv
  exact hdiv

end Work.Diff.C
