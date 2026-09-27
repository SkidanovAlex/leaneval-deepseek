import Mathlib

namespace Work.EKLNonExc

open Polynomial

/-- A rational real number which is a root of the monic integer polynomial
`X^3 - b * X + 2` is an integer. -/
theorem int_of_rat_root (lam : ℝ) (b : ℤ) (hq : ∃ q : ℚ, (q : ℝ) = lam)
    (hroot : lam ^ 3 = (b : ℝ) * lam - 2) : ∃ m : ℤ, (m : ℝ) = lam := by
  obtain ⟨q, rfl⟩ := hq
  -- transfer the root equation from `ℝ` to `ℚ`
  have hq0 : q ^ 3 - (b : ℚ) * q + 2 = 0 := by
    have h : ((q ^ 3 - (b : ℚ) * q + 2 : ℚ) : ℝ) = 0 := by
      push_cast
      linear_combination hroot
    exact_mod_cast h
  -- `q` is a root of the monic polynomial `X^3 - C b * X + C 2` over `ℤ`
  have hroot' : (Polynomial.aeval q)
      (Polynomial.X ^ 3 - Polynomial.C b * Polynomial.X + Polynomial.C 2 : Polynomial ℤ) = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    exact hq0
  -- integral root theorem
  obtain ⟨z, hz⟩ := isInteger_of_is_root_of_monic (A := ℤ) (K := ℚ) (by monicity!) hroot'
  refine ⟨z, ?_⟩
  rw [← hz]
  simp

end Work.EKLNonExc
