import Mathlib
import Submission.Work.C17.local_tools

/-!
# The local expansion of `rhoQ` at `x = 0`

`rhoQ = (x-1)² / (x² - 2x) = (x-1)²/(x(x-2))`, so near `x = 0`

  `rhoQ = x^{-1}·(-1/2 + (3/4)·x + O(x²))`,

i.e. `Lead2At rhoQ (-1) (-1/2) (3/4)`.  Concretely
`rhoQ·x + 1/2 - (3/4)·x = x²/(4(x-2))`, and `1/(4(x-2))` is regular at `0`.
-/

namespace Work.C17

open Commons.FieldTheory.RatFunc

noncomputable section

theorem lead2_rhoQ : Lead2At rhoQ (-1) (-1/2) (3/4) := by
  refine lead2At_of_eq rhoQ (-1) (-1/2) (3/4) (by norm_num)
    (g := algebraMap ℚ (RatFunc ℚ) (1 / 4) / (xQ - 2)) ?_ ?_
  · -- `1/(4(x-2))` is regular at `0`: it is a quotient of polynomial images
    -- whose denominator does not vanish at `0`.
    have h := reg_div_algebraMap_local_tools (p := Polynomial.C (1 / 4))
      (q := Polynomial.X - Polynomial.C 2) (by simp)
    simpa [xQ, map_sub, ← algQ_eq_algP] using h
  · -- the two-term expansion: `rhoQ·x + 1/2 - (3/4)·x = x²·(1/(4(x-2)))`
    have hx0 : (xQ : RatFunc ℚ) ≠ 0 := xQ_ne_zero_local_tools
    have hx2 : (xQ - 2 : RatFunc ℚ) ≠ 0 := by
      have h2 : (xQ - 2 : RatFunc ℚ)
          = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - Polynomial.C 2) := by
        simp [xQ, map_sub]
      rw [h2]
      exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero (2 : ℚ))
    rw [show (algebraMap ℚ (RatFunc ℚ) (-1 / 2)) = (-1 / 2 : RatFunc ℚ) by norm_num,
      show (algebraMap ℚ (RatFunc ℚ) (3 / 4)) = (3 / 4 : RatFunc ℚ) by norm_num,
      show (algebraMap ℚ (RatFunc ℚ) (1 / 4)) = (1 / 4 : RatFunc ℚ) by norm_num]
    simp only [neg_neg, zpow_one]
    rw [show rhoQ = (xQ - 1) ^ 2 / (xQ ^ 2 - 2 * xQ) from rfl]
    field_simp [hx0, hx2]
    ring

end

end Work.C17
