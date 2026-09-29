import Mathlib

namespace Work.Fx

/-- The phase `2πi·j/k` of a root of unity depends only on `j mod k`: `exp` has period
`2πi`, and `j = (j.fmod k) + k * (j.fdiv k)`. -/
theorem CisPhase (j : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / (k : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * ((Int.fmod j k : ℤ) : ℂ) / (k : ℂ)) := by
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine Complex.exp_eq_exp_iff_exists_int.mpr ⟨j.fdiv (k : ℤ), ?_⟩
  have hC : (j : ℂ) = ((Int.fmod j k : ℤ) : ℂ) + (k : ℂ) * ((j.fdiv (k : ℤ) : ℤ) : ℂ) := by
    exact_mod_cast (Int.fmod_add_mul_fdiv j (k : ℤ)).symm
  rw [hC]
  field_simp

end Work.Fx
