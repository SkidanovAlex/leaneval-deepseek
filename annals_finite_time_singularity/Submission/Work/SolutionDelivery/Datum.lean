/-
# `Work.SolutionDelivery.Datum` — the decay clause for a compactly supported vorticity

The `α`-power decay clause of the challenge is *automatic* for a bounded vorticity of compact
support (`vorticityDecay_of_support_bdd`): this is what makes the decay clause of
`AssemblyInputs` free for the cut-off datum `ω₀ = χ(ρ/L)·ωS`.  The assembly of the four datum
clauses themselves is in `Work.SolutionDelivery.DatumEuler`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SolutionDelivery.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

/-- **The `α`-power decay of the vorticity is automatic for a bounded compactly supported field.**

If `ω` vanishes outside `B(0,R)` and is bounded by `M`, then `‖ω x‖ ≤ C/(‖x‖^α + 1)` for every
`x`, with `C = max 1 (M(R^α+1))`: outside the ball both sides vanish, and inside it
`‖x‖^α + 1 ≤ R^α + 1` so that `M ≤ C/(‖x‖^α+1)`. -/
theorem vorticityDecay_of_support_bdd {α : NNReal} {ω : R3 → R3} {R M : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hsupp : ∀ y : R3, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hbdd : ∀ y : R3, ‖ω y‖ ≤ M) :
    Work.LWP.VorticityDecay α ω := by
  refine ⟨max 1 (M * (R ^ (α : ℝ) + 1)), lt_of_lt_of_le one_pos (le_max_left _ _), fun x => ?_⟩
  rcases eq_or_ne (ω x) 0 with h0 | hne
  · rw [h0, norm_zero]
    positivity
  · have hxmem : x ∈ Metric.closedBall (0 : R3) R := hsupp x hne
    rw [Metric.mem_closedBall, dist_zero_right] at hxmem
    have hxα : ‖x‖ ^ (α : ℝ) ≤ R ^ (α : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg x) hxmem (by positivity)
    have hden : 0 < ‖x‖ ^ (α : ℝ) + 1 := by
      have := Real.rpow_nonneg (norm_nonneg x) (α : ℝ); linarith
    have hdenR : 0 < R ^ (α : ℝ) + 1 := by
      have := Real.rpow_nonneg hR (α : ℝ); linarith
    rw [le_div_iff₀ hden]
    have h1 : M * (R ^ (α : ℝ) + 1) ≤ max 1 (M * (R ^ (α : ℝ) + 1)) := le_max_right _ _
    have h2 : 1 ≤ max 1 (M * (R ^ (α : ℝ) + 1)) := le_max_left _ _
    nlinarith [hbdd x, h1, h2, hdenR, hxα, Real.rpow_nonneg (norm_nonneg x) (α : ℝ)]

end Work.SolutionDelivery
