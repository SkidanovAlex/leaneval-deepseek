import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixGlue.Residuals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Pot.ellB_ge`

The dilute-regime large-box condition `R ≤ ℓ(μ)·chiR0` together with the box side's positivity,
uniformly for all sufficiently small diluteness `μ·(a v)³`.

This is the bare-parameter growth statement `Work.BoseBox.sideAt_large` (the box side
`ℓ(μ) = sideAt μ (a v) = a (μ a³)^{-163/323}` blows up as `μ → 0⁺`) read off at
`ℓB v μ := sideAt μ (a v)` and `r₀ := chiR0`, exactly as parts of
`Work.BoseFixGlue.Pot.potInput_holds` do.
-/

namespace Work.BoseFixGlue.Pot

open MeasureTheory Filter Metric
open scoped Topology BigOperators

set_option linter.unusedVariables false

theorem ellB_ge {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hav : 0 < BoseGases.a v) (hR : 0 < R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * (BoseGases.a v) ^ 3 ≤ ε₀ →
      0 < Work.BoseFixGlue.ℓB v μ ∧ R ≤ Work.BoseFixGlue.ℓB v μ * Submission.BoseGases.chiR0 := by
  -- `ℓ(μ) = sideAt μ (a v)` blows up as `μ → 0⁺`, so `R ≤ ℓ(μ)·chiR0` eventually.
  have hev := Work.BoseBox.sideAt_large (a := BoseGases.a v) hav R Submission.BoseGases.chiR0
    Submission.BoseGases.chiR0_pos
  rw [eventually_nhdsWithin_iff] at hev
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  -- the threshold: `μa³ ≤ ε₀` forces `μ ≤ δ/2 < δ`
  have ha3 : 0 < (BoseGases.a v) ^ 3 := pow_pos hav 3
  refine ⟨min 1 (δ * (BoseGases.a v) ^ 3 / 2), lt_min one_pos (by positivity), ?_⟩
  intro μ hμpos ht
  have htδ : μ * (BoseGases.a v) ^ 3 ≤ δ * (BoseGases.a v) ^ 3 / 2 :=
    le_trans ht (min_le_right _ _)
  have hμδ : μ < δ := by nlinarith [ha3, hδpos]
  refine ⟨Work.BoseBox.sideAt_pos hμpos hav, ?_⟩
  have h := hδ (y := μ) (by rw [Real.dist_eq, sub_zero, abs_of_pos hμpos]; exact hμδ) hμpos
  simpa [Work.BoseFixGlue.ℓB] using h

end Work.BoseFixGlue.Pot
