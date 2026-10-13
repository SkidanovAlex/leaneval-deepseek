import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.aesm_uncurry_restrict_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

theorem aesmPzMulSinCos2Box {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {a b : ℝ} (ha : 0 < a) :
    MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- `0 < a` forces `(a,b] ⊆ (0,∞)`, so the domain `(a,b] × Iθ` is covered by the open
  -- quadrant `(0,∞) × (0,π/2)` up to the null set `(a,b] × {0, π/2}`.  On the open quadrant
  -- the integrand is continuous: `∂_zΨ` is (`SmoothOpen.pz`) and `θ ↦ sinθcos²θ` is.
  refine Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ ?_ ha.le
  have h2 : Continuous fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2 := by
    unfold Work.Elliptic.sinCos2; fun_prop
  exact (show ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 from (hΨ.pz).continuousOn).mul h2.continuousOn

end Work.FTS.EllipticEst.remov.SourceBound
