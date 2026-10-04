import Mathlib
import Submission.Work.Diff.C.model_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

theorem modelF_hasDerivAt_zero {a u κ : ℝ} (ha0 : 0 < a) (haπ : a < Real.pi) :
    HasDerivAt (modelF a u κ) (-(u * κ)) 0 := by
  -- `0 < sin a` and `-1 < cos a < 1` for `a ∈ (0, π)`
  have hsin : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 haπ
  have hcos_lt_one : Real.cos a < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := a) le_rfl haπ.le ha0
    rwa [Real.cos_zero] at h
  have hcos_gt_neg_one : -1 < Real.cos a := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := a) (y := Real.pi) ha0.le le_rfl haπ
    rwa [Real.cos_pi] at h
  -- `modelG a u κ 0 = cos a` avoids `±1`
  have h1 : modelG a u κ 0 ≠ -1 := by rw [modelG_zero]; linarith
  have h2 : modelG a u κ 0 ≠ 1 := by rw [modelG_zero]; linarith
  -- chain rule: `arccos ∘ modelG`
  have hcomp := (Real.hasDerivAt_arccos h1 h2).comp 0 (modelG_hasDerivAt a u κ 0)
  -- evaluate the derivative
  have hval : -(1 / Real.sqrt (1 - (modelG a u κ 0) ^ 2)) * modelD a u κ 0 = -(u * κ) := by
    rw [modelG_zero, modelD_zero]
    have hsinsq : 1 - Real.cos a ^ 2 = Real.sin a ^ 2 := by
      have h := Real.sin_sq_add_cos_sq a; linarith
    rw [hsinsq, Real.sqrt_sq hsin.le]
    field_simp
  rw [hval] at hcomp
  convert hcomp using 1
  ext s
  rfl

end Work.Diff.C
