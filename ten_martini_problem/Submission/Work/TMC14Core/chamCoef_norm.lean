import Mathlib
import Submission.Work.TMC14Core.RatRot

namespace Work.TMC14Core

/-- The oscillatory coefficient `chamCoef p q lam = 2(-λ)^q(-1)^{p(q-1)}` has
complex norm `2 λ^q` for `λ > 0`. -/
theorem chamCoef_norm (p : ℤ) (q : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    ‖Work.TMC14Core.chamCoef p q lam‖ = 2 * lam ^ q := by
  have h0 : ‖(lam : ℂ)‖ = lam :=
    (RCLike.norm_ofReal lam).trans (abs_of_pos hlam)
  have h1 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have h2 : ‖(-(lam : ℂ)) ^ q‖ = lam ^ q := by
    rw [norm_pow, norm_neg, h0]
  have h3 : ‖(-1 : ℂ) ^ (p * ((q : ℤ) - 1))‖ = 1 := by
    rw [norm_zpow, norm_neg, norm_one, one_zpow]
  rw [Work.TMC14Core.chamCoef, norm_mul, norm_mul, h1, h2, h3, mul_one]

end Work.TMC14Core
