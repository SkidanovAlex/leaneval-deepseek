import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

open scoped Matrix

/-- The limit shape `[[1,p,q],[0,1,0],[0,r,1]]` is the product
`u_01(p) * u_21(r) * u_02(q)` of the three root-group elements. -/
theorem uparShape_eq_prod (p q r : ℝ) :
    uparShape p q r = uij h01 p * uij h21 r * uij h02 q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uij, uparShape, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_three]

theorem uparShape_mem (p q r : ℝ) : uparShape p q r ∈ Upar h01 h02 h21 := by
  rw [uparShape_eq_prod]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨p, rfl⟩))
  · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨r, rfl⟩)
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨q, rfl⟩))

end Work.EKLC8Core
