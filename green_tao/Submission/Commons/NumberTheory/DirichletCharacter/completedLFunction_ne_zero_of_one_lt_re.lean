import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace Commons.NumberTheory.DirichletCharacter

theorem completedLFunction_ne_zero_of_one_lt_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) : DirichletCharacter.completedLFunction χ s ≠ 0 := by
  intro h0
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have h := _root_.DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
  rw [h0, zero_div] at h
  exact (_root_.DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inr hs1)
    (le_of_lt hs)) h

end Commons.NumberTheory.DirichletCharacter