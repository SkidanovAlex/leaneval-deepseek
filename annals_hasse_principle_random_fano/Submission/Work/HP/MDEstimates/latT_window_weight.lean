import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.kwin_spec
import Submission.Work.HP.ceil_logb_bounds
import Submission.Work.HP.MDEstimates.two_pow_ceillogb_sq_le
import Submission.Work.HP.MDEstimates.weight_arith

/-!
# The dyadic-window weight bound (`Work.HP.MDEstimates.latT_window_weight`)

For a rank-`3` lattice `L ⊆ ℤ^5` whose first two successive minima are at most `Z ≥ 1`, the
dyadic-window weight

`(1 + Z/λ₁)² (1 + Z/λ₂)²`

is bounded by `256 Z⁴ / (2^{2⌈log₂ λ₁⌉} · 2^{2⌈log₂ λ₂⌉})`.

Indeed `λ_i ≥ 1` (as `1 ≤ i ≤ rk L = 3`), so `λ_i ≤ Z` gives `Z/λ_i ≥ 1` and hence
`(1 + Z/λ_i)² ≤ 4 Z²/λ_i²`; the two factors combine to `16 Z⁴/(λ₁²λ₂²)`.  On the other side
`2^{⌈log₂ λ_i⌉} ≤ 2 λ_i`, so `2^{2⌈log₂ λ_i⌉} ≤ 4 λ_i²` and the denominator of the right-hand
side is at most `16 λ₁²λ₂²`, making the right-hand side at least `16 Z⁴/(λ₁²λ₂²)`.  The two
estimates meet, with equality possible at `λ₁ = λ₂ = Z = 1`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.MDEstimates

open Work.HP

theorem latT_window_weight (Z : ℝ) (hZ : 1 ≤ Z) (L : Submodule ℤ (Fin 5 → ℤ)) (hrk : rk L = 3)
    (h1 : lam L 1 ≤ Z) (h2 : lam L 2 ≤ Z) :
    (1 + Z / lam L 1) ^ 2 * (1 + Z / lam L 2) ^ 2
      ≤ 256 * Z ^ 4 / ((2:ℝ) ^ (2 * ⌈Real.logb 2 (lam L 1)⌉₊) * (2:ℝ) ^ (2 * ⌈Real.logb 2 (lam L 2)⌉₊)) := by
  -- the two successive minima are at least `1` because `1, 2 ≤ rk L = 3`
  have h1ge : 1 ≤ lam L 1 := one_le_lam L (i := 1) le_rfl (by rw [hrk]; norm_num)
  have h2ge : 1 ≤ lam L 2 := one_le_lam L (i := 2) (by norm_num) (by rw [hrk]; norm_num)
  -- the dyadic windows are at most twice the corresponding successive minimum
  have hA : (2:ℝ) ^ (2 * ⌈Real.logb 2 (lam L 1)⌉₊) ≤ 4 * (lam L 1) ^ 2 :=
    two_pow_ceillogb_sq_le _ h1ge
  have hB : (2:ℝ) ^ (2 * ⌈Real.logb 2 (lam L 2)⌉₊) ≤ 4 * (lam L 2) ^ 2 :=
    two_pow_ceillogb_sq_le _ h2ge
  have hApos : 0 < (2:ℝ) ^ (2 * ⌈Real.logb 2 (lam L 1)⌉₊) := by positivity
  have hBpos : 0 < (2:ℝ) ^ (2 * ⌈Real.logb 2 (lam L 2)⌉₊) := by positivity
  exact weight_arith Z (lam L 1) (lam L 2) _ _ hZ h1ge h2ge h1 h2 hA hB hApos hBpos

end Work.HP.MDEstimates
