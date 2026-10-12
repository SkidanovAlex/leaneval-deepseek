import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB1.RegimeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.Regime

open Work.BoseBox

/-- FS's regime: the healing-length box `ℓ = K_ℓ(μa)^{-1/2}` (with FS's `K_ℓ`) is at least
the mean interparticle spacing `μ^{-1/3}` whenever the diluteness is at most one.

Both sides are closed monomials at `t = μ A³`: `μ^{-1/3} = A t^{-1/3}` and
`ℓ = A t^{-163/323}`, and `-1/3 ≥ -163/323`. -/
theorem inv_third_le_sideAt {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) (ht : μ * A ^ 3 ≤ 1) : μ ^ (-(1 / 3) : ℝ) ≤ sideAt μ A := by
  have ht0 : 0 < μ * A ^ 3 := by positivity
  rw [Work.BoseFixB1.mu_inv_third_eq hA hμ, Work.BoseFixB1.sideAt_eq_fsXp hA hμ]
  refine mul_le_mul_of_nonneg_left ?_ hA.le
  exact fsXp_le_fsXp ht0 ht (by norm_num)

end Work.BoseFixB1.Regime
