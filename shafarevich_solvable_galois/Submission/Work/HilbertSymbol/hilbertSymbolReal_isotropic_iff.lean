/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Isotropy of `x ^ 2 - a y ^ 2 - b z ^ 2` over `ℝ` and the archimedean Hilbert symbol

The archimedean Hilbert symbol `(a,b)_∞` is `-1` exactly when `a < 0` and `b < 0`
(`hilbertSymbolReal_eq_neg_one_iff`), and `1` otherwise.  The nondegenerate ternary quadratic
form `⟨1, -a, -b⟩`, i.e. `q(x,y,z) = x ^ 2 - a y ^ 2 - b z ^ 2`, is isotropic over `ℝ` (has a
nonzero zero) precisely in the complementary case.  Indeed

* if `a ≥ 0` then `(√a, 1, 0)` is a nonzero zero of `q`;
* if `a < 0` then `(a,b)_∞ = -1` forces `b ≥ 0`, and `(√b, 0, 1)` is a nonzero zero of `q`;
* if `a < 0` and `b < 0` then `q(x,y,z) = x ^ 2 + (-a) y ^ 2 + (-b) z ^ 2 ≥ 0` vanishes only
  for `x = y = z = 0`.

We prove the clean statement for `A B : ℚ` (the case needed, with the comparison carried out
in `ℚ` so that it matches `hilbertSymbolReal_eq_one_iff` verbatim), and deduce the criterion
for `hilbertSymbolReal`.
-/
import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- The ternary quadratic form `x ^ 2 - A y ^ 2 - B z ^ 2` over `ℝ` is isotropic (has a nonzero
zero) if and only if `A` and `B` are not both negative. -/
lemma exists_isotropic_vector_iff_rat (A B : ℚ) :
    (∃ x y z : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      x ^ 2 - (A : ℝ) * y ^ 2 - (B : ℝ) * z ^ 2 = 0) ↔ ¬(A < 0 ∧ B < 0) := by
  constructor
  · rintro ⟨x, y, z, hne, h⟩ ⟨hA, hB⟩
    have hA' : (A : ℝ) < 0 := by exact_mod_cast hA
    have hB' : (B : ℝ) < 0 := by exact_mod_cast hB
    have hAy : (A : ℝ) * y ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt hA') (sq_nonneg y)
    have hBz : (B : ℝ) * z ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt hB') (sq_nonneg z)
    have hx2 : x ^ 2 ≤ 0 := by linarith
    have hx : x = 0 := sq_eq_zero_iff.mp (le_antisymm hx2 (sq_nonneg x))
    subst hx
    have hAy0 : (A : ℝ) * y ^ 2 = 0 := by linarith
    have hy : y = 0 := by
      rcases mul_eq_zero.mp hAy0 with h' | h'
      · exact absurd h' (ne_of_lt hA')
      · exact sq_eq_zero_iff.mp h'
    subst hy
    have hz : z = 0 := by
      have hBz0 : (B : ℝ) * z ^ 2 = 0 := by linarith
      rcases mul_eq_zero.mp hBz0 with h' | h'
      · exact absurd h' (ne_of_lt hB')
      · exact sq_eq_zero_iff.mp h'
    subst hz
    rcases hne with h' | h' | h' <;> exact h' rfl
  · intro h
    by_cases hA : (0 : ℚ) ≤ A
    · refine ⟨Real.sqrt (A : ℝ), 1, 0, Or.inr (Or.inl one_ne_zero), ?_⟩
      have hA' : (0 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
      rw [Real.sq_sqrt hA']
      ring
    · have hAlt : A < 0 := not_le.mp hA
      have hBge : (0 : ℚ) ≤ B := not_lt.mp fun hBlt => h ⟨hAlt, hBlt⟩
      have hBge' : (0 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hBge
      refine ⟨Real.sqrt (B : ℝ), 0, 1, Or.inr (Or.inr one_ne_zero), ?_⟩
      rw [Real.sq_sqrt hBge']
      ring

theorem hilbertSymbolReal_isotropic_iff (a b : ℚˣ) :
    hilbertSymbolReal a b = 1 ↔
      ∃ x y z : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
        x ^ 2 - ((a : ℚ) : ℝ) * y ^ 2 - ((b : ℚ) : ℝ) * z ^ 2 = 0 := by
  rw [hilbertSymbolReal_eq_one_iff]
  exact (exists_isotropic_vector_iff_rat ((a : ℚ)) ((b : ℚ))).symm

end Work.HilbertSymbol
