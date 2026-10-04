/-
# The periodic coefficient matrix on the `2σ`-ball

`Work.Diff.STE.B3.tmA φ lam' γ = lam' • 1 + per (φ · (γ - lam' • 1))` is the globally smooth,
`1`-periodic matrix built from the *local* coefficient family `γ`; the transport identity only knows
`γ` on a neighbourhood of the `2σ j`-ball.  This file proves that on the region where the cutoff
`φ` is identically `1` and the only non-vanishing translate of `φ` is the trivial one, `tmA φ lam' γ`
agrees with `γ` itself — this is the identification `A = γ` used when the transport identity is
discharged.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.tmA_props

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace Work.Diff.STE.B3

set_option maxHeartbeats 1000000

/-- **`tmA φ lam' γ` agrees with `γ` where `φ ≡ 1` and the periodisation is a single translate.**

If `Function.support φ ⊆ Metric.ball 0 R` with `R ≤ 1/2` (so that two translates of `φ` can never
both be non-zero at the same point, and the only non-zero translate at a point of the ball of radius
`ρ ≤ R` is the trivial one) and `φ ≡ 1` on the closed ball of radius `ρ`, then for `‖z‖ ≤ ρ`

`tmA φ lam' γ z = γ z`. -/
lemma tmA_eq_of_one {n : ℕ} {R ρ lam' : ℝ} (φ : (Fin n → ℝ) → ℝ)
    (γ : (Fin n → ℝ) → Fin n → Fin n → ℝ) (hR : R ≤ 1 / 2) (hρR : ρ ≤ R)
    (hφsupp : Function.support φ ⊆ Metric.ball 0 R)
    (hφ1 : ∀ w : Fin n → ℝ, ‖w‖ ≤ ρ → φ w = 1)
    {z : Fin n → ℝ} (hz : ‖z‖ ≤ ρ) (p q : Fin n) :
    tmA φ lam' γ z p q = γ z p q := by
  rw [tmA_eq_govIdx φ γ hR hφsupp z p q]
  have hz0 : φ z ≠ 0 := by rw [hφ1 z hz]; norm_num
  have hgov : govIdx φ z = 0 := by
    by_contra h
    have h0 : φ (z + iVec (0 : Fin n → ℤ)) = 0 := govIdx_spec hR hφsupp z 0 (Ne.symm h)
    rw [show z + iVec (0 : Fin n → ℤ) = z from by simp [iVec]] at h0
    exact hz0 h0
  rw [hgov]
  rw [show z + iVec (0 : Fin n → ℤ) = z from by simp [iVec]]
  rw [hφ1 z hz]
  ring

end Work.Diff.STE.B3
