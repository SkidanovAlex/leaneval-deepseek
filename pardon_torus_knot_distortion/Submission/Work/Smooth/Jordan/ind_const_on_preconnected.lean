import Mathlib
import Submission.Work.Smooth.Jordan.JordanIndex
import Submission.Work.Smooth.Jordan.ind_local

/-!
# The index is constant on preconnected sets off the trace

The index `ind c` of a smooth closed curve is locally constant on the complement of the trace
(`Work.Smooth.Jordan.ind_local`).  Consequently it is constant on every preconnected subset of
that complement.
-/

open Set

namespace Work.Smooth.Jordan

noncomputable section

/-- **The index of a smooth plane curve is constant on a preconnected set off its trace.**

Since `ind c` is locally constant on `c.traceᶜ` (each point has a ball on which it is constant,
`Work.Smooth.Jordan.ind_local`), and a locally constant function on a preconnected space is
constant, `ind c` takes the same value at any two points of a preconnected `W ⊆ c.traceᶜ`. -/
theorem ind_const_on_preconnected (c : SmoothPlaneCurve) {W : Set ℂ} (hW : IsPreconnected W)
    (hsub : W ⊆ c.traceᶜ) {x y : ℂ} (hx : x ∈ W) (hy : y ∈ W) : ind c x = ind c y := by
  haveI : PreconnectedSpace W := isPreconnected_iff_preconnectedSpace.mp hW
  have hlc : IsLocallyConstant (fun z : W => ind c (z : ℂ)) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro z
    obtain ⟨ε, hε, hconst⟩ := ind_local c (hsub z.2)
    refine ⟨{w : W | (w : ℂ) ∈ Metric.ball (z : ℂ) ε}, ?_, ?_, ?_⟩
    · exact Metric.isOpen_ball.preimage continuous_subtype_val
    · exact Metric.mem_ball_self hε
    · intro w hw
      exact hconst (w : ℂ) hw
  exact hlc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

end

end Work.Smooth.Jordan
