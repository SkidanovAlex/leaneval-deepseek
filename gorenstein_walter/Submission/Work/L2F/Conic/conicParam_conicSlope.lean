import Mathlib
import Submission.Work.L2F.Conic.Param

namespace Work.L2F.Conic

theorem conicParam_conicSlope (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) {p : F × F}
    (hp : p.1 ^ 2 + p.2 ^ 2 = 1) : conicParam F (conicSlope F p) = p := by
  by_cases h : p.2 = 1
  · -- `p = (0,1)`, the point represented by `none`.
    have hp1 : p.1 ^ 2 = 0 := by
      have hh := hp
      rw [h] at hh
      simp only [one_pow] at hh
      linear_combination hh
    have hp0 : p.1 = 0 := sq_eq_zero_iff.mp hp1
    have hpe : p = (0, 1) := by ext <;> simp [hp0, h]
    rw [hpe]
    simp [conicSlope, conicParam]
  · -- `t = p.1/(1-p.2)` is the slope; a direct computation gives `t ^ 2 + 1 = 2/(1-p.2)`.
    have hden : 1 - p.2 ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hkey : (p.1 / (1 - p.2)) ^ 2 + 1 = 2 / (1 - p.2) := by
      field_simp
      linear_combination hp
    have hfst : 2 * (p.1 / (1 - p.2)) / ((p.1 / (1 - p.2)) ^ 2 + 1) = p.1 := by
      rw [hkey]
      field_simp
    have hsnd : ((p.1 / (1 - p.2)) ^ 2 - 1) / ((p.1 / (1 - p.2)) ^ 2 + 1) = p.2 := by
      rw [hkey]
      field_simp
      linear_combination hp
    simp only [conicSlope]
    rw [ite_eq_right h]
    simp only [conicParam]
    rw [hfst, hsnd]

end Work.L2F.Conic
