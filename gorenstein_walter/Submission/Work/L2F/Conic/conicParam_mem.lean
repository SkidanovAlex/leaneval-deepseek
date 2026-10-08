import Mathlib
import Submission.Work.L2F.Conic.Param

namespace Work.L2F.Conic

theorem conicParam_mem (F : Type*) [Field F] (h : ∀ i : F, i * i ≠ -1) (m : Option F) :
    (conicParam F m).1 ^ 2 + (conicParam F m).2 ^ 2 = 1 := by
  cases m with
  | none => simp [conicParam]
  | some t =>
    have ht : t ^ 2 + 1 ≠ 0 := by
      intro hc
      apply h t
      have h2 : t ^ 2 = -1 := by linear_combination hc
      rwa [sq] at h2
    simp only [conicParam]
    field_simp
    ring

end Work.L2F.Conic
