import Mathlib
import Submission.Work.L2F.Conic.Param

namespace Work.L2F.Conic

/-- A point of the plane whose second coordinate is not `1` has a well defined slope
`p.1 / (1 - p.2)`. -/
theorem conicSlope_eq_some {F : Type*} [Field F] (p : F × F) (hp : p.2 ≠ 1) :
    conicSlope F p = some (p.1 / (1 - p.2)) := by
  rw [conicSlope, ite_eq_right hp]

theorem conicSlope_conicParam (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (h : ∀ i : F, i * i ≠ -1) (m : Option F) : conicSlope F (conicParam F m) = m := by
  cases m with
  | none => simp [conicParam, conicSlope]
  | some t =>
    have ht : t ^ 2 + 1 ≠ 0 := by
      intro hc
      exact h t (by linear_combination hc)
    have hne : (t ^ 2 - 1) / (t ^ 2 + 1) ≠ 1 := by
      intro hc
      have heq : t ^ 2 - 1 = t ^ 2 + 1 := (div_eq_one_iff_eq ht).mp hc
      exact h2 (by linear_combination -heq)
    rw [conicParam, conicSlope_eq_some _ hne]
    congr 1
    have hden : 1 - (t ^ 2 - 1) / (t ^ 2 + 1) = 2 / (t ^ 2 + 1) := by
      field_simp
      ring
    rw [hden]
    field_simp

end Work.L2F.Conic
