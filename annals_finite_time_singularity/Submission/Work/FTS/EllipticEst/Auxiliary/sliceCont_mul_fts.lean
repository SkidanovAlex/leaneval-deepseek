import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Spaces.HardyZ
import Submission.Work.Coercivity.contDiffOn_infty_integral_Itheta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Auxiliary

/-- The angular interval `Iθ = [0,π/2]` sits inside the `θ`-range of the
neighbourhood `U = (-1,∞) × (-1,π/2+1)` on which `SmoothNbhd` grants smoothness. -/
private theorem ioi_prod_Iθ_subset_U :
    Set.Ioi (-1) ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.U := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  obtain ⟨h0, h1⟩ := hp.2
  have hpi := Real.pi_pos
  exact ⟨by linarith, by linarith⟩

/-- **Continuity of the angular slice integral of a product.**  If `u` and `v` are smooth
on a neighbourhood of the closed quadrant, then `z ↦ ∫_θ u z θ · v z θ dθ` is continuous
on `(-1,∞)`.  Indeed `(z,θ) ↦ u z θ · v z θ` is jointly continuous on
`(-1,∞) × [0,π/2]`, so this is the parametric-integral continuity lemma
`continuousOn_integral_Itheta_of_continuousOn`. -/
theorem sliceCont_mul_fts (u v : ℝ → ℝ → ℝ) (hu : Work.Spaces.SmoothNbhd u) (hv : Work.Spaces.SmoothNbhd v) : ContinuousOn (fun z => ∫ θ in Work.Spaces.Iθ, u z θ * v z θ) (Set.Ioi (-1)) := by
  refine Work.Coercivity.continuousOn_integral_Itheta_of_continuousOn isOpen_Ioi ?_
  have h1 : ContinuousOn (Function.uncurry u) (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) :=
    (hu.mono ioi_prod_Iθ_subset_U).continuousOn
  have h2 : ContinuousOn (Function.uncurry v) (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) :=
    (hv.mono ioi_prod_Iθ_subset_U).continuousOn
  exact h1.mul h2

end Work.FTS.EllipticEst.Auxiliary
