import Mathlib
import Submission.Work.HP.LsetAux.GridDefs

/-!
# The arithmetic grid inequality

With `gEps n N C2 = 4 C₂ (n+1) / N²` and `gDel n N C1 = 2 C₁ √(n+1) / N` (see `GridDefs.lean`),
the product appearing in the grid-covering argument is bounded by the "slab" normalisation:

`(2N+1)^{n+1} · K · gEps · gDel^n ≤ 3^{n+1} · K · 4 C₂ (n+1) · (2 C₁ √(n+1))^n / N`.

Indeed both sides equal `((2N+1)/N)^{n+1}` resp. `3^{n+1}` times the common positive factor
`K · 4 C₂ (n+1) · (2 C₁ √(n+1))^n / N`, and `(2N+1)/N ≤ 3` because `N ≥ 1`.
-/

set_option autoImplicit false
noncomputable section
open Classical Finset MvPolynomial MeasureTheory
open scoped BigOperators ENNReal

namespace Work.HP.LsetAux

theorem grid_arith (n N : ℕ) {K C1 C2 : ℝ} (hK : 0 < K) (hC1 : 0 < C1) (hC2 : 0 < C2)
    (hN : 1 ≤ N) :
    (2 * (N : ℝ) + 1) ^ (n + 1) * K * gEps n N C2 * (gDel n N C1) ^ n
      ≤ (3 ^ (n + 1) * K * 4 * C2 * ((n : ℝ) + 1) *
            (2 * C1 * Real.sqrt ((n : ℝ) + 1)) ^ n) / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hNge : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- Both sides, written with the common factor `K · 4 C₂ (n+1) · (2 C₁ √(n+1))^n / N`.
  have hL : (2 * (N : ℝ) + 1) ^ (n + 1) * K * gEps n N C2 * (gDel n N C1) ^ n
      = ((2 * (N : ℝ) + 1) / (N : ℝ)) ^ (n + 1) *
        (K * 4 * C2 * ((n : ℝ) + 1) * (2 * C1 * Real.sqrt ((n : ℝ) + 1)) ^ n / (N : ℝ)) := by
    rw [gEps, gDel]
    simp only [div_pow]
    field_simp
    ring_nf
  have hR : (3 ^ (n + 1) * K * 4 * C2 * ((n : ℝ) + 1) *
        (2 * C1 * Real.sqrt ((n : ℝ) + 1)) ^ n) / (N : ℝ)
      = 3 ^ (n + 1) * (K * 4 * C2 * ((n : ℝ) + 1) *
        (2 * C1 * Real.sqrt ((n : ℝ) + 1)) ^ n / (N : ℝ)) := by ring
  rw [hL, hR]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine pow_le_pow_left₀ ?_ ?_ (n + 1)
  · exact div_nonneg (by positivity) (le_of_lt hNpos)
  · rw [div_le_iff₀ hNpos]
    linarith

end Work.HP.LsetAux
