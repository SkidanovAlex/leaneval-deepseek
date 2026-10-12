import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `sideAt_ge_of_dilute`

The dilute-regime large-box condition `R ≤ ℓ(μ)·chiR0` for the `B3` box side
`ℓ(μ) = ℓB3 μ (a v) = sideAt μ (a v)`, uniformly for all sufficiently small
diluteness `μ·(a v)³ ≤ ε₀` (with `ε₀ ≤ 1`).

This is the bare-parameter growth statement `Work.BoseBox.sideAt_large` — the
box side `ℓ(μ) = a·(μa³)^(-163/323)` blows up as `μ → 0⁺`, because both factors
`K_ℓ = (μa³)^(-3/646) → ∞` and `(μa)^(-1/2) → ∞` do — read off at
`a := a v` and `r₀ := chiR0`, in the vocabulary of `Work.BoseFixB3.ellAt`.  The
`ε₀` supplied is the threshold produced by `sideAt_large`, capped at `1`.
-/

namespace Work.BoseFixB3.Eps

open MeasureTheory Filter Metric
open scoped Topology

/-- **Dilute-regime large box at the `B3` parameters.**  For every fixed support
radius `R > 0` there is a diluteness threshold `ε₀ ∈ (0,1]` such that for all
`μ > 0` with `μ·(a v)³ ≤ ε₀` the box side `ellAt μ (a v)` is large enough that
`R ≤ ellAt μ (a v) · chiR0`. -/
theorem sideAt_ge_of_dilute (v : EuclideanSpace ℝ (Fin 3) → ℝ) (hav : 0 < BoseGases.a v)
    {R : ℝ} (hR : 0 < R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ μ : ℝ, 0 < μ → μ * (BoseGases.a v) ^ 3 ≤ ε₀ →
      R ≤ Work.BoseFixB3.ellAt μ (BoseGases.a v) * Submission.BoseGases.chiR0 := by
  -- `ℓ(μ) = sideAt μ (a v)` blows up as `μ → 0⁺`, so `R ≤ ℓ(μ)·chiR0` eventually.
  have hev := Work.BoseBox.sideAt_large (a := BoseGases.a v) hav R Submission.BoseGases.chiR0
    Submission.BoseGases.chiR0_pos
  rw [eventually_nhdsWithin_iff] at hev
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  -- the threshold: `μa³ ≤ ε₀` will force `μ ≤ δ/2 < δ`, capped at `1`
  have ha3 : 0 < (BoseGases.a v) ^ 3 := pow_pos hav 3
  refine ⟨min 1 (δ * (BoseGases.a v) ^ 3 / 2), lt_min one_pos (by positivity),
    min_le_left _ _, ?_⟩
  intro μ hμpos ht
  have htδ : μ * (BoseGases.a v) ^ 3 ≤ δ * (BoseGases.a v) ^ 3 / 2 :=
    le_trans ht (min_le_right _ _)
  have hμδ : μ < δ := by nlinarith [ha3, hδpos]
  have h := hδ (y := μ)
    (by rw [Real.dist_eq, sub_zero, abs_of_pos hμpos]; exact hμδ) hμpos
  simpa only [Work.BoseFixB3.ellAt] using h

end Work.BoseFixB3.Eps
