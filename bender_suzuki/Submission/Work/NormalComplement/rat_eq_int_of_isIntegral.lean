import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- Integrality over `ℤ` descends from `ℂ` to `ℚ` along the injective algebra map `ℚ → ℂ`. -/
theorem isIntegral_rat_of_isIntegral_complex {q : ℚ} (h : IsIntegral ℤ (q : ℂ)) :
    IsIntegral ℤ q :=
  (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℂ)).mp (by simpa using h)

/-- A rational number integral over `ℤ` is an integer: `ℤ` is integrally closed in `ℚ`. -/
theorem rat_eq_int_of_isIntegral {q : ℚ} (h : IsIntegral ℤ (q : ℂ)) : ∃ m : ℤ, q = (m : ℚ) := by
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_rat_of_isIntegral_complex h)
  exact ⟨m, by rw [← hm]; simp⟩

end Work.NormalComplement
