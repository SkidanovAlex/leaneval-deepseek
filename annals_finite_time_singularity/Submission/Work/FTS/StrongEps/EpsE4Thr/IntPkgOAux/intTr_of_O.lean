import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux

theorem intTr_of_O {u : Work.FTS.Galerkin.Fn} {ρ : Work.FTS.Galerkin.Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen u)
    (hρc : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.CoercivityFix.Coer1.Qd)
    (hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (hsq : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => u z θ ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hth : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth u z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ * ρ z θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  -- Continuity of the unweighted product on the open quadrant, from `SmoothOpen u` and `hρc`.
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.Dth u p.1 p.2 * u p.1 p.2 * ρ p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
    (((hs.Dth).continuousOn).mul hs.continuousOn).mul hρc
  -- The product of two `L²`-blocks is integrable: `2|ab| ≤ a² + b²` and `ρ ≥ 0` on `Iθ`.
  exact Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q
    (Work.FTS.CoercivityFix.Coer1.integrableOn_mul_of_sq_Q hcont hρnn hth hsq)

end Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux
