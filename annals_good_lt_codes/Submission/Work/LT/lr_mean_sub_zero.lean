import Mathlib

namespace Work.LT

/-- Subtracting the mean makes a function mean-zero. -/
theorem lr_mean_sub_zero {X : Type} [Fintype X] (f : X → ℝ) :
    ∑ x, (f x - (∑ y, f y) / (Fintype.card X : ℝ)) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  by_cases h : (Fintype.card X : ℝ) = 0
  · have hE : IsEmpty X := Fintype.card_eq_zero_iff.mp (by exact_mod_cast h)
    rw [Finset.univ_eq_empty_iff.mpr hE, Finset.sum_empty]
    simp
  · rw [mul_div_cancel₀ _ h]
    exact sub_self _

end Work.LT
