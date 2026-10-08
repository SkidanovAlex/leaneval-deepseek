import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff

namespace Work.L2F.PSL

/-- In odd characteristic, two elements of `SL(2,F)` have the same image in `PSL(2,F)` exactly
when they differ by the central element `-1`. -/
theorem pslMap_eq_iff (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (x y : Matrix.SpecialLinearGroup (Fin 2) F) :
    Work.PSL2.pslMap F x = Work.PSL2.pslMap F y ↔ x = y ∨ x = Work.L2F.negOne F * y := by
  -- `-1` has trivial image, since the kernel of `pslMap` is the centre `{1, -1}`.
  have hneg : Work.PSL2.pslMap F (Work.L2F.negOne F) = 1 :=
    (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (Work.L2F.negOne F)).mpr (Or.inr rfl)
  constructor
  · intro h
    -- `pslMap x = pslMap y` gives `pslMap (x * y⁻¹) = 1`, so `x * y⁻¹ ∈ {1, -1}`.
    have hxy : Work.PSL2.pslMap F (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (x * y⁻¹)).mp hxy with h1 | h1
    · left
      rwa [mul_inv_eq_one] at h1
    · right
      have := congrArg (fun z => z * y) h1
      rwa [mul_assoc, inv_mul_cancel, mul_one] at this
  · rintro (rfl | h)
    · rfl
    · rw [h, map_mul, hneg, one_mul]

end Work.L2F.PSL
