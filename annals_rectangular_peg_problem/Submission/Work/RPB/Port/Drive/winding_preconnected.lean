import Mathlib
import Submission.Work.RPB.Port.Drive.WindingNumber
import Submission.Work.RPB.Port.Drive.winding_ball

namespace Work.RPB.Port.Drive

open scoped Topology

/-- **The winding number is constant on preconnected pieces of the complement of the curve.**

If `C` is a preconnected subset of `(range γ)ᶜ`, then `q ↦ winding γ hγ (hC q.2)` is constant on `C`:
by `Work.RPB.Port.Drive.exists_ball_winding_eq` that function is locally constant in the point, so the points
of `C` where it takes a fixed value are clopen in `C`.

This is the first half of the classical statement that the winding number of a simple closed curve is
`0` outside and `±1` inside: constancy on the connected components of the complement, leaving only the
value to be computed.

Proof note: prove `IsLocallyConstant` of `F : C → ℤ`, `F x = winding γ hγ (hC x.2)`, using the ball
from `exists_ball_winding_eq` at `x.1` intersected with `C`; then apply
`IsLocallyConstant.apply_eq_of_isPreconnected`.  (Extending `F` by `0` off the curve and working on
the ambient space does *not* work: that extension is not locally constant at points of `range γ`.) -/
theorem winding_preconnected {γ : UnitAddCircle → ℝ × ℝ} (hγ : Continuous γ)
    {C : Set (ℝ × ℝ)} (hC : C ⊆ (Set.range γ)ᶜ) (hconn : IsPreconnected C) (q q' : C) :
    winding γ hγ (hC q'.2) = winding γ hγ (hC q.2) := by
  -- The function `F` on `C` whose value at `x` is the winding number about `x`.
  let F : C → ℤ := fun x => winding γ hγ (hC x.2)
  -- `F` is locally constant: at each `x` the ball of `exists_ball_winding_eq` gives a neighbourhood
  -- on which `F y = F x`.
  have hloc : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨r, hr, hball⟩ := exists_ball_winding_eq γ hγ (hC x.2)
    have hU : {y : C | (y : ℝ × ℝ) ∈ Metric.ball (x : ℝ × ℝ) r} ∈ 𝓝 x :=
      (continuous_subtype_val.continuousAt).preimage_mem_nhds (Metric.ball_mem_nhds _ hr)
    filter_upwards [hU] with y hy
    show F y = F x
    exact hball (y : ℝ × ℝ) hy (hC y.2)
  -- A preconnected subset is a preconnected topological space.
  have hpc : PreconnectedSpace C := Subtype.preconnectedSpace hconn
  exact (hloc.apply_eq_of_preconnectedSpace q q').symm

end Work.RPB.Port.Drive
