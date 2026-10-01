import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_le_inv_sub_one

namespace Commons.NumberTheory.DirichletCharacter

/--
Explicit bound for a Dirichlet `L`-function on the half-plane `Re s ≥ 2`:
`‖LFunction χ s‖ ≤ 2`.

This follows from `LFunction_norm_le_inv_sub_one`, which bounds
`‖L(χ, σ + iT)‖ ≤ 1 + 1/(σ - 1)` for `σ > 1`; for `σ ≥ 2` this equals at most `2`.
-/
theorem LFunction_norm_le_two_of_two_le_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ) (hs : 2 ≤ s.re) : ‖DirichletCharacter.LFunction χ s‖ ≤ 2 := by
  have hσ : (1 : ℝ) < s.re := by linarith
  have hs_split : s = (s.re : ℂ) + Complex.I * (s.im : ℂ) := by
    apply Complex.ext <;> simp
  have hbound := LFunction_norm_le_inv_sub_one (N := N) χ (σ := s.re) (T := s.im) hσ
  rw [hs_split]
  have h2 : 1 + 1 / (s.re - 1) ≤ 2 := by
    have hpos : 0 < s.re - 1 := by linarith
    have h1 : 1 / (s.re - 1) ≤ 1 := by
      rw [div_le_iff₀ hpos]
      linarith
    linarith
  linarith

end Commons.NumberTheory.DirichletCharacter
