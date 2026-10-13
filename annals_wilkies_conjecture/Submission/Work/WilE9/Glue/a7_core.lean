import Mathlib

namespace Work.WilE9.Glue

/-
  Denominator-clearing equivalence for the difference quotient, including the degenerate case
  `h = 0` (where Lean's `b / 0 = 0` makes the right-hand side `|a| < ε`).
-/
theorem a7_core (a b h ε : ℝ) :
    (0 < ε ∧ ((h ≠ 0 ∧ 0 < ε ^ 2 * h ^ 2 - (a * h - b) ^ 2) ∨ (h = 0 ∧ a ^ 2 < ε ^ 2))) ↔
      |a - b / h| < ε := by
  constructor
  · rintro ⟨hε, ⟨hhne, hineq⟩ | ⟨hh0, hineq⟩⟩
    · have hsq : (a * h - b) ^ 2 < (ε * h) ^ 2 := by nlinarith [hineq]
      have hlt : |a * h - b| < ε * |h| := by
        have h1 := sq_lt_sq.mp hsq
        rwa [abs_mul, abs_of_pos hε] at h1
      have hpos : 0 < |h| := abs_pos.mpr hhne
      have hrw : a - b / h = (a * h - b) / h := by
        rw [sub_div, mul_div_cancel_right₀ a hhne]
      rw [hrw, abs_div, div_lt_iff₀ hpos]
      exact hlt
    · subst hh0
      simp only [div_zero, sub_zero]
      have h1 := sq_lt_sq.mp hineq
      rwa [abs_of_pos hε] at h1
  · intro hlt
    have hε : 0 < ε := lt_of_le_of_lt (abs_nonneg _) hlt
    refine ⟨hε, ?_⟩
    rcases eq_or_ne h 0 with hh0 | hhne
    · subst hh0
      right
      refine ⟨rfl, ?_⟩
      simp only [div_zero, sub_zero] at hlt
      have h1 : |a| < |ε| := by rwa [abs_of_pos hε]
      exact sq_lt_sq.mpr h1
    · left
      refine ⟨hhne, ?_⟩
      have hpos : 0 < |h| := abs_pos.mpr hhne
      have hrw : a - b / h = (a * h - b) / h := by
        rw [sub_div, mul_div_cancel_right₀ a hhne]
      rw [hrw, abs_div, div_lt_iff₀ hpos] at hlt
      have hsq : (a * h - b) ^ 2 < (ε * |h|) ^ 2 := by
        apply sq_lt_sq.mpr
        rwa [abs_of_nonneg (by positivity : (0:ℝ) ≤ ε * |h|)]
      rw [mul_pow, sq_abs] at hsq
      linarith

end Work.WilE9.Glue
