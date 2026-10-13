import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.SolutionDelivery.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Holder

open Set

/-- `IsContDiffHolderOn ℝ α f` is monotone in the set: if `f ∈ C^{1,α}(s)` and `s' ⊆ s` is
such that every point of `s'` is a unique differentiability point of `s'` (so that the
within-derivative on `s'` is the honest one), then `f ∈ C^{1,α}(s')`.

The point of the hypothesis `hun'` is that on `s'` the *within* derivative `fderivWithin ℝ f s'`
computes the same operator as `fderivWithin ℝ f s`: this is `fderivWithin_subset`, which needs
`UniqueDiffWithinAt ℝ s' p` and differentiability of `f` on the larger set `s`.  Note that no
uniqueness hypothesis on `s` itself is needed. -/
theorem isContDiffHolderOn_mono {α : NNReal} {f : Work.SolutionDelivery.R3 × ℝ → Work.SolutionDelivery.R3}
    {s s' : Set (Work.SolutionDelivery.R3 × ℝ)}
    (h : IsContDiffHolderOn ℝ α f s) (hsub : s' ⊆ s)
    (hun' : ∀ p ∈ s', UniqueDiffWithinAt ℝ s' p) :
    IsContDiffHolderOn ℝ α f s' := by
  obtain ⟨hcd, hbdd, hhold⟩ := h
  -- `f` is differentiable on `s`, hence within-differentiable at each point of `s ⊆ s`.
  have hdiff : DifferentiableOn ℝ f s := hcd.differentiableOn (by norm_num)
  -- On `s'` the two within-derivatives agree.
  have hkey : ∀ x ∈ s', fderivWithin ℝ f s' x = fderivWithin ℝ f s x :=
    fun x hx => fderivWithin_subset hsub (hun' x hx) (hdiff x (hsub hx))
  refine ⟨hcd.mono hsub, ?_, ?_⟩
  · -- Boundedness of the within-derivative is inherited, since `s' ⊆ s`.
    refine hbdd.subset ?_
    rw [show fderivWithin ℝ f s' '' s' = fderivWithin ℝ f s '' s' from Set.image_congr hkey]
    exact Set.image_mono hsub
  · -- The Hölder constant is inherited verbatim.
    obtain ⟨C, hC⟩ := hhold
    exact ⟨C, fun x hx y hy => by
      rw [hkey x hx, hkey y hy]
      exact hC x (hsub hx) y (hsub hy)⟩

end Work.SolutionDelivery.Holder
