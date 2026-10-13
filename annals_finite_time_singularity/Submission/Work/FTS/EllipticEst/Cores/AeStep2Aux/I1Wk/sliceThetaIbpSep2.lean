import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.SliceThetaIbpDefs
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_identity
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_trunc
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.sliceThetaIbpSep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

theorem sliceThetaIbpSep2 (v ψ : ℝ → ℝ)
    (hv : ContDiffOn ℝ 2 v (Set.Ioo 0 (Real.pi / 2)))
    (hψ : ContDiff ℝ 2 ψ)
    (hsep : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2 ∧ tsupport ψ ⊆ Set.Ioo a b) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (v θ * deriv (deriv v) θ))
      = -2 * Work.Spaces.eta * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (v θ) ^ 2)
        - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (deriv v θ) ^ 2)
        - (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * ψ θ
              * (deriv v θ - (1 + Work.Spaces.eta) * v θ * Real.cos (2 * θ)
                  * (Real.sin (2 * θ)) ^ (-(1 : ℝ))) ^ 2)
        + (1 / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * deriv (deriv ψ) θ * (v θ) ^ 2) := by
  exact sliceThetaIbpSep v ψ hv hψ hsep

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
