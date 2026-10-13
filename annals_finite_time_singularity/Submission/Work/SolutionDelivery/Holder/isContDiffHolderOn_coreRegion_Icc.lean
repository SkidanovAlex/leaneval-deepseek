import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.SolutionDelivery.Defs
import Submission.Work.SolutionDelivery.Holder.isContDiffHolderOn_mono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Holder

open Set
open scoped Topology

/-!
# Core-restricting a joint `C^{1,α}` bound: `univ × Icc` gives `coreRegion ρ × Icc`

The challenge hypothesis is the joint `C^{1,α}` regularity of `u.uncurry` on the *whole* spatial
space over the time interval `[0,S]`.  The core regularity statements of the construction, on the
other hand, are asked on the core strip `coreRegion ρ ×ˢ Icc 0 S`, i.e. on the closed spatial ball
of radius `ρ`.  This file records the (purely set-theoretic, given the uniqueness of the
within-derivative) passage from the first to the second.

The one point that is not automatic is that the derivative is taken *within* the set
(`fderivWithin`): for `t` on the spatial boundary of the core strip, or for `t = 0` or `t = S`,
the two `fderivWithin`s are related by `fderivWithin_subset`, which needs
`UniqueDiffWithinAt` of the *smaller* set.  That uniqueness holds because `coreRegion ρ` is a
closed ball with `ρ > 0` (convex, with nonempty interior, so `uniqueDiffWithinAt_convex` applies
at every point of its closure) and `Icc 0 S` has `0 < S`.
-/

/-- Every point of the core strip `coreRegion ρ ×ˢ Icc 0 S` is a point of unique differentiability
of that strip, when `ρ > 0` and `S > 0`. -/
theorem uniqueDiffWithinAt_coreRegion_prod_Icc {ρ S : ℝ} (hρ : 0 < ρ) (hS : 0 < S) :
    ∀ p ∈ Work.StabilityFar.coreRegion ρ ×ˢ Set.Icc 0 S,
      UniqueDiffWithinAt ℝ (Work.StabilityFar.coreRegion ρ ×ˢ Set.Icc 0 S) p := by
  intro p hp
  obtain ⟨hpx, hpt⟩ := hp
  refine UniqueDiffWithinAt.prod ?_ (uniqueDiffOn_Icc hS p.2 hpt)
  have hball : Work.StabilityFar.coreRegion ρ
      = Metric.closedBall (0 : Work.SolutionDelivery.R3) ρ := by
    ext y
    rw [Work.StabilityFar.mem_coreRegion, Metric.mem_closedBall, dist_eq_norm]
    simp
  rw [hball] at hpx ⊢
  refine uniqueDiffWithinAt_convex (convex_closedBall _ _) ?_ (subset_closure hpx)
  rw [interior_closedBall _ (ne_of_gt hρ)]
  exact ⟨0, by simp [Metric.mem_ball, hρ]⟩

theorem isContDiffHolderOn_coreRegion_Icc {α : NNReal}
    {u : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3} {ρ S : ℝ}
    (hρ : 0 < ρ) (hS : 0 < S)
    (h : IsContDiffHolderOn ℝ α u.uncurry (Set.univ ×ˢ Set.Icc 0 S)) :
    IsContDiffHolderOn ℝ α u.uncurry
      (Work.StabilityFar.coreRegion ρ ×ˢ Set.Icc 0 S) := by
  obtain ⟨hcd, hbdd, hholder⟩ := h
  have hsub : Work.StabilityFar.coreRegion ρ ×ˢ Set.Icc 0 S ⊆ Set.univ ×ˢ Set.Icc 0 S :=
    fun p hp => ⟨trivial, hp.2⟩
  have hdiff : DifferentiableOn ℝ u.uncurry (Set.univ ×ˢ Set.Icc 0 S) :=
    hcd.differentiableOn (by norm_num)
  have huniq := uniqueDiffWithinAt_coreRegion_prod_Icc (S := S) hρ hS
  -- the two `fderivWithin`s agree on the core strip
  have hderiv : ∀ p ∈ (Work.StabilityFar.coreRegion ρ ×ˢ Set.Icc 0 S),
      fderivWithin ℝ u.uncurry (Work.StabilityFar.coreRegion ρ ×ˢ Set.Icc 0 S) p
        = fderivWithin ℝ u.uncurry (Set.univ ×ˢ Set.Icc 0 S) p :=
    fun p hp => fderivWithin_subset hsub (huniq p hp) (hdiff p (hsub hp))
  refine ⟨hcd.mono hsub, ?_, ?_⟩
  · exact hbdd.subset (fun y hy => by
      obtain ⟨p, hp, rfl⟩ := hy
      exact ⟨p, hsub hp, (hderiv p hp).symm⟩)
  · obtain ⟨C, hC⟩ := hholder
    exact ⟨C, fun p hp q hq => by
      rw [hderiv p hp, hderiv q hq]
      exact hC.edist_le (hsub hp) (hsub hq)⟩

end Work.SolutionDelivery.Holder
