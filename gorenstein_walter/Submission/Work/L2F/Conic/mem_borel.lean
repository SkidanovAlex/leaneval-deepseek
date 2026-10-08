import Mathlib
import Submission.Work.L2F.Defs

namespace Work.L2F.Conic

open Matrix

/-- The upper triangular matrices of `SL(2,F)` form a subgroup: the entry `1 0` of a product is
`x 1 0 * y 0 0 + x 1 1 * y 1 0`, and the entry `1 0` of the inverse is `-x 1 0`. -/
def upperTriSubgroup (F : Type*) [Field F] : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) where
  carrier := {x | (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hx, hy]
    simp
  one_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [Matrix.SpecialLinearGroup.coe_one]
    simp
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [hx]

/-- Membership in `borel F` (the closure of the upper triangular matrices): exactly the upper
triangular matrices.  The set `{x | (x : Matrix _ _ F) 1 0 = 0}` is closed under multiplication and
inverses (for `2 × 2` matrices with `det = 1`, the entry `1 0` of the inverse is `-x 1 0`), so the
closure is the set itself. -/
theorem mem_borel (F : Type*) [Field F] (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    x ∈ Work.L2F.borel F ↔ (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  constructor
  · intro hx
    exact (Subgroup.closure_le (upperTriSubgroup F)).mpr (fun _ hy => hy) hx
  · intro hx
    exact Subgroup.subset_closure hx

end Work.L2F.Conic
