import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex DirichletCharacter
open scoped Real

namespace Commons.NumberTheory.DirichletCharacter

/-- Uniform polynomial bound for the Dirichlet L-function of a primitive non-trivial
character of modulus `N` in the strip `1/8 ≤ Re s ≤ 1`:
`‖L(s,χ)‖ ≤ 16 · (1+|Im s|) · N`. -/
theorem LFunction_uniform_poly_strip {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, (1 / 8 : ℝ) ≤ s.re → s.re ≤ 1 →
      ‖DirichletCharacter.LFunction χ s‖ ≤ C * (1 + |s.im|) ^ k * (N : ℝ) ^ k := by
  refine ⟨16, 1, by norm_num, by norm_num, ?_⟩
  intro s hs_low hs_high
  have hs0 : 0 < s.re := lt_of_lt_of_le (by norm_num) hs_low
  have hs_nonneg : 0 ≤ s.re := le_of_lt hs0
  have hs_abs : |s.re| ≤ 1 := by
    rw [abs_of_nonneg hs_nonneg]
    exact hs_high
  have htri := Complex.norm_le_abs_re_add_abs_im s
  have hnorm : ‖s‖ ≤ 1 + |s.im| := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := htri
      _ ≤ 1 + |s.im| := add_le_add hs_abs le_rfl
  have hb := LFunction_norm_half_plane χ hχ hs0
  have hmain : 2 * (N : ℝ) * ‖s‖ / s.re ≤ 16 * (N : ℝ) * (1 + |s.im|) := by
    have hinv : (s.re)⁻¹ ≤ 8 := by
      have hle : 1 / s.re ≤ 8 := by
        have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (1 / 8 : ℝ)) hs_low
        simpa using h
      simpa using hle
    calc
      2 * (N : ℝ) * ‖s‖ / s.re
          ≤ 2 * (N : ℝ) * ‖s‖ * 8 := by
              rw [div_eq_mul_inv]
              gcongr
      _ ≤ 16 * (N : ℝ) * (1 + |s.im|) := by
              calc
                2 * (N : ℝ) * ‖s‖ * 8 = 16 * (N : ℝ) * ‖s‖ := by ring
                _ ≤ 16 * (N : ℝ) * (1 + |s.im|) := by
                    gcongr
  calc
    ‖DirichletCharacter.LFunction χ s‖ ≤ 2 * (N : ℝ) * ‖s‖ / s.re := hb
    _ ≤ 16 * (N : ℝ) * (1 + |s.im|) := hmain
    _ = 16 * (1 + |s.im|) ^ (1 : ℝ) * (N : ℝ) ^ (1 : ℝ) := by
        simp
        ring

end Commons.NumberTheory.DirichletCharacter
