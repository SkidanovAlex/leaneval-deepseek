import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

/-- `Uij h` is exactly the range of the one-parameter subgroup `s ↦ uij h s`; indeed the
range is already a subgroup, since `uij h 0 = 1`, `uij h (s+t) = uij h s * uij h t` and
`(uij h s)⁻¹ = uij h (-s)`. -/
theorem mem_Uij (g : SL3) {i j : Fin 3} (h : i ≠ j) :
    (g ∈ Uij h ↔ ∃ s : ℝ, uij h s = g) := by
  constructor
  · intro hg
    let S : Subgroup SL3 :=
      { carrier := Set.range fun s : ℝ => uij h s
        one_mem' := ⟨0, by simp [uij, Matrix.SpecialLinearGroup.transvection_coeff_zero]⟩
        mul_mem' := by
          rintro a b ⟨s, rfl⟩ ⟨t, rfl⟩
          exact ⟨s + t, by simp [uij, Matrix.SpecialLinearGroup.transvection_add]⟩
        inv_mem' := by
          rintro a ⟨s, rfl⟩
          exact ⟨-s, by simp [uij, Matrix.SpecialLinearGroup.transvection_inv]⟩ }
    have hle : Uij h ≤ S := (Subgroup.closure_le S).2 (fun x hx => hx)
    exact hle hg
  · rintro ⟨s, rfl⟩
    exact Subgroup.subset_closure (Set.mem_range_self s)

end Work.EKLC8Core
