import Mathlib
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs

namespace Work.L2F.Props

/-- The product of two elements of the "reflection coset"
`cmtK1 F S = {x ∈ SL(2,F) | x S x⁻¹ = -S}` lies in the centralizer `cmtK0 F S`: if
`x S x⁻¹ = -S` and `y S y⁻¹ = -S` then `(x * y) S (x * y)⁻¹ = x (y S y⁻¹) x⁻¹ = x (-S) x⁻¹ =
-(x S x⁻¹) = S`.  Proof: `mem_cmtK1_iff`, `mem_cmtK0_iff`, `conj_mul_eq`, `conj_negGL`,
`negGL_negGL`, `Matrix.SpecialLinearGroup.coe_mul`. -/
theorem cmtK1_mul_mem_cmtK0 (F : Type*) [Field F] (S : Matrix.GeneralLinearGroup (Fin 2) F) :
    ∀ x y : Matrix.SpecialLinearGroup (Fin 2) F,
      x ∈ Work.L2F.Props.cmtK1 F S → y ∈ Work.L2F.Props.cmtK1 F S →
        x * y ∈ Work.L2F.Props.cmtK0 F S := by
  intro x y hx hy
  rw [mem_cmtK0_iff, mem_cmtK1_iff] at *
  rw [conj_mul_eq F x y S, hy, conj_negGL, hx, negGL_negGL]

end Work.L2F.Props
