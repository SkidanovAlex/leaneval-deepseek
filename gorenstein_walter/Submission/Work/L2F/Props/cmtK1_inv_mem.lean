import Mathlib
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs

namespace Work.L2F.Props

/-- The "reflection coset" `cmtK1 F S = {x ∈ SL(2,F) | x S x⁻¹ = -S}` is closed under inversion:
`x S x⁻¹ = -S` implies `S = x⁻¹ (-S) x = -(x⁻¹ S x)`, so `x⁻¹ S x = -S`, i.e.
`x⁻¹ S (x⁻¹)⁻¹ = -S`.  This is the existing lemma `conj_inv_of_eq_neg` repackaged via
`mem_cmtK1_iff`. -/
theorem cmtK1_inv_mem (F : Type*) [Field F] (S : Matrix.GeneralLinearGroup (Fin 2) F) :
    ∀ x : Matrix.SpecialLinearGroup (Fin 2) F,
      x ∈ Work.L2F.Props.cmtK1 F S → x⁻¹ ∈ Work.L2F.Props.cmtK1 F S := by
  intro x hx
  rw [mem_cmtK1_iff] at hx ⊢
  exact conj_inv_of_eq_neg F x S hx

end Work.L2F.Props
