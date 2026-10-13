import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.InteriorRegularity.Q0.RRDefs
import Submission.Work.EllipticEst.InteriorRegularity.bslOp_comp_exp
import Submission.Work.EllipticEst.InteriorRegularity.IR.integralQ0eqStrip
import Submission.Work.EllipticEst.InteriorRegularity.Q0.pullbackExists
import Submission.Work.EllipticEst.InteriorRegularity.Q0.transportWeakRRAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

theorem transportWeakRR {α : ℝ} (hα : 0 < α) {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0,
          Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        = ∫ p in Work.FTS.EllipticEst.Q0,
            F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) :
    Work.EllipticEst.InteriorRegularity.Q0.StripWeakRR
      (fun σ θ => (Work.EllipticEst.InteriorRegularity.Q0.VRR α Ψ σ θ : ℂ))
      (fun σ θ => (Work.EllipticEst.InteriorRegularity.Q0.GRR α F σ θ : ℂ)) :=
  transportWeakRR_of_pullback hα hΨ hweak
    (fun ψ h1 h2 h3 => pullbackExists hα h1 h2 h3)

end Work.EllipticEst.InteriorRegularity.Q0
