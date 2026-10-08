import Mathlib
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs
import Submission.Work.L2F.Props.toPGL_mem_ker_iff

namespace Work.L2F.Props

open scoped MatrixGroups
open Matrix

/-- The image in `GL(2,F)` of the matrix `-1` of `SL(2,F)` is `negOneGL F`: both are the unit
whose underlying matrix is `-1`. -/
theorem toGL_negOne_eq_negOneGL (F : Type*) [Field F] :
    Matrix.SpecialLinearGroup.toGL (Work.L2F.negOne F) = negOneGL F :=
  Units.ext rfl

/-- `-1` lies in every centralizer `cmtK0 F A`, because it is central in `GL(2,F)`. -/
theorem negOne_mem_cmtK0 (F : Type*) [Field F] (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    Work.L2F.negOne F ∈ cmtK0 F A := by
  rw [mem_cmtK0_iff_comm, toGL_negOne_eq_negOneGL F, negOneGL_mul_comm]

/-- FILE `Submission/Work/L2F/Props/le_cmtK0_of_map_toPGL_eq.lean`, in `namespace Work.L2F.Props`.
If the images in `PGL(2,F)` of the centralizers `cmtK0 F S` and `cmtK0 F A` of two elements of `GL(2,F)` coincide, then the centralizers themselves satisfy `cmtK0 F S ≤ cmtK0 F A`.  Reason: `ker (toPGL : SL(2,F) → PGL(2,F)) = {±1}` (`Work.L2F.Props.toPGL_mem_ker_iff`), and `-1` is central, hence lies in every `cmtK0`. -/
theorem le_cmtK0_of_map_toPGL_eq (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (S A : Matrix.GeneralLinearGroup (Fin 2) F)
    (h : (Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL =
      (Work.L2F.Props.cmtK0 F A).map Matrix.SpecialLinearGroup.toPGL) :
    Work.L2F.Props.cmtK0 F S ≤ Work.L2F.Props.cmtK0 F A := by
  intro x hx
  -- `toPGL x` lies in the image of `cmtK0 F A`, so it is the image of some `y ∈ cmtK0 F A`.
  have hx' : Matrix.SpecialLinearGroup.toPGL x ∈
      (Work.L2F.Props.cmtK0 F A).map Matrix.SpecialLinearGroup.toPGL := by
    rw [← h]
    exact ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hx'
  -- then `y⁻¹ * x ∈ ker toPGL = {±1}`, so `x = y` or `x = y * (-1)`.
  have hker : Matrix.SpecialLinearGroup.toPGL (y⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, hyx, inv_mul_cancel]
  have hfac : x = y * (y⁻¹ * x) := by group
  rcases (Work.L2F.Props.toPGL_mem_ker_iff F h2 (y⁻¹ * x)).mp hker with h1 | h1
  · rw [hfac, h1, mul_one]
    exact hy
  · rw [hfac, h1]
    exact mul_mem hy (negOne_mem_cmtK0 F A)

end Work.L2F.Props
