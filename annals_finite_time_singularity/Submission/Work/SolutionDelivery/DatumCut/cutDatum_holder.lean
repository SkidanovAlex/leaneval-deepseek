import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SolutionDelivery.DatumCut

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.DatumCut

/-- **The cut-off datum is `α`-Hölder** whenever `ω` is `C^{1,α}` and `α ≤ 1`.

`cutDatum L ω = χ(ρ/L) • ω` is the cut-off of `ω`, and `Work.Stability.OmegaCutHolder` shows
that the cut-off of a `C^{1,α}` field is again `C^{1,α}` (the cut-off factor `x ↦ χ(ρ(x)/L)` is
`C^∞`, bounded, with compactly supported bounded Lipschitz derivative, and `α ≤ 1`).  A `C^{1,α}`
field has in particular a bounded derivative, hence is Lipschitz (`LipschitzOfBoundedFderiv`);
the cut-off is supported in the ball of radius `2L`, hence bounded; and by
`HolderOfBoundedLipschitz` a bounded Lipschitz function is `α`-Hölder for every `α ≤ 1`. -/
theorem cutDatum_holder {L : ℝ} (hL : 0 < L) {α : NNReal} (hα : 0 < α) (hα1 : α ≤ 1)
    {ω : Work.SolutionDelivery.R3 → Work.SolutionDelivery.R3}
    (h : IsContDiffHolder ℝ α ω) :
    Holder α (Work.SolutionDelivery.cutDatum L ω) := by
  -- the cut-off of a `C^{1,α}` field is `C^{1,α}`
  have hcut : IsContDiffHolder ℝ α (Work.SolutionDelivery.cutDatum L ω) :=
    Work.Stability.OmegaCutHolder hL hα1 h
  -- hence its derivative is bounded, so it is Lipschitz
  have hdiff : Differentiable ℝ (Work.SolutionDelivery.cutDatum L ω) :=
    hcut.1.differentiable one_ne_zero
  obtain ⟨K, hK⟩ := Work.Stability.LipschitzOfBoundedFderiv hdiff hcut.2.1
  -- and it is bounded, being continuous and supported in the ball of radius `2L`
  have hbdd : IsBoundedFun (Work.SolutionDelivery.cutDatum L ω) := by
    refine Work.Stability.isBoundedFun_of_continuous_of_eq_zero_of_norm_gt
      hcut.1.continuous (R := 2 * L) ?_
    intro x hx
    by_contra hne
    have hmem := Work.SolutionDelivery.cutDatum_support hL x hne
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    linarith
  exact Work.Stability.HolderOfBoundedLipschitz hα1 hbdd hK

end Work.SolutionDelivery.DatumCut
