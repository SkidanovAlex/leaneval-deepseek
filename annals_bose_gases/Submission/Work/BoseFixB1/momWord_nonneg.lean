import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

theorem momWord_nonneg {ℓ d εT b : ℝ} (hb : 0 ≤ b) (hε : 0 ≤ εT)
    (u : EuclideanSpace ℝ (Fin 3)) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    0 ≤ Work.BoseKinLoc.momWord ℓ d εT b u ψ := by
  unfold Work.BoseKinLoc.momWord
  -- `(d*ℓ)^(-2) = ((d*ℓ)^2)⁻¹ ≥ 0`, unconditionally: no sign hypothesis on `d*ℓ` is needed.
  have hz : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := by
    rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
    positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg hb hε) hz) (Work.BoseKinLoc.momForm_nonneg u ψ)

end Work.BoseFixB1
