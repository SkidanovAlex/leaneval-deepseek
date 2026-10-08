import Mathlib
import Submission.Work.L2F.Defs

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Mat2

/-- The kernel of `SL(2,F) → PSL(2,F)` in odd characteristic is `{1, -1}`:
`QuotientGroup.ker_mk'` reduces it to the centre computation (commute a generic matrix with
`!![1,1;0,1]` and `!![1,0;1,1]` to see that a central element is scalar `λ • 1`, and `det = 1`
gives `λ² = 1`, so `λ = ±1` since `(2:F) ≠ 0`). -/
theorem pslMap_eq_one_iff (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    Work.PSL2.pslMap F x = 1 ↔ x = 1 ∨ x = Work.L2F.negOne F := by
  -- The whole content is the computation of the centre of `SL(2,F)`:
  -- `Matrix.SpecialLinearGroup.mem_center_iff` says a central element is a scalar matrix
  -- `scalar (Fin 2) r` whose scalar `r` satisfies `r ^ 2 = 1`; over a field `r ^ 2 = 1`
  -- factors as `(r - 1) * (r + 1) = 0`, so `r = 1` or `r = -1`.
  have hcenter : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ↔
      x = 1 ∨ x = Work.L2F.negOne F := by
    constructor
    · intro hx
      rw [Matrix.SpecialLinearGroup.mem_center_iff] at hx
      obtain ⟨r, hr2, hrA⟩ := hx
      have hr2' : r ^ 2 = 1 := by simpa using hr2
      have hfac : (r - 1) * (r + 1) = 0 := by
        have h : (r - 1) * (r + 1) = r ^ 2 - 1 := by ring
        rw [h, hr2', sub_self]
      rcases mul_eq_zero.mp hfac with h | h
      · left
        have hr1 : r = 1 := sub_eq_zero.mp h
        apply Subtype.ext
        rw [← hrA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]
      · right
        have hr1 : r = -1 := by
          rw [add_eq_zero_iff_eq_neg] at h; exact h
        apply Subtype.ext
        rw [← hrA, hr1,
          show ((Work.L2F.negOne F : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) = -1 from rfl,
          map_neg, map_one]
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        change ((g * Work.L2F.negOne F : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) =
          ((Work.L2F.negOne F * g : SL(2,F)) : Matrix (Fin 2) (Fin 2) F)
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
          show ((Work.L2F.negOne F : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
        simp
  -- `pslMap` is by definition `QuotientGroup.mk' (center …)`, and the kernel of `mk'` is that
  -- centre (`QuotientGroup.ker_mk'`), so `pslMap x = 1 ↔ x ∈ center`.
  change QuotientGroup.mk' (Subgroup.center (SL(2, F))) x = 1 ↔ x = 1 ∨ x = Work.L2F.negOne F
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  exact hcenter

end Work.L2F.Mat2
