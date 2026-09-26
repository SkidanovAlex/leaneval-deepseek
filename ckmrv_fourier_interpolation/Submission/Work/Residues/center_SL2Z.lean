import Mathlib

namespace Work.Residues

/-- The center of `SL(2, ℤ)` consists of the two elements `±1`. -/
theorem center_SL2Z {A : Matrix.SpecialLinearGroup (Fin 2) ℤ} :
    A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) ℤ) ↔ A = 1 ∨ A = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hrA⟩
    have hr' : r = 1 ∨ r = -1 := by
      have h2 : r ^ 2 = 1 := by simpa using hr
      exact sq_eq_one_iff.mp h2
    obtain h | h := hr'
    · left
      subst h
      rw [map_one] at hrA
      exact Subtype.ext hrA.symm
    · right
      subst h
      rw [map_neg, map_one] at hrA
      exact Subtype.ext hrA.symm
  · rintro (h | h)
    · refine ⟨1, by norm_num, ?_⟩
      rw [h, map_one, Matrix.SpecialLinearGroup.coe_one]
    · refine ⟨-1, by norm_num, ?_⟩
      rw [h, map_neg, map_one, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one]

end Work.Residues
