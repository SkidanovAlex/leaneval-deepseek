import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.LzeroAdj_sinCos2
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoZeroOfMoment

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

/-- **Left-end pointwise vanishing from the angular moment condition.**

The integrand `θ ↦ Lzero1 u θ · sinθcos²θ` is an exact `θ`-derivative
(`Work.Elliptic.hasDerivAt_Lzero_antideriv`): with the antiderivative
`A(θ) = -u'(θ) sinθcos²θ + u(θ) cosθ cos 2θ`,

  `∫_{Iθ} Lzero1 u · sinθcos²θ = A(π/2) - lim_{0⁺} A = -lim_{0⁺} u`,

because `A(π/2) = 0` (`sinθcos²θ` and `cosθcos2θ` both vanish at `π/2`) and
`A(θ) → lim_{0⁺} u` as `θ → 0⁺` (`sinθcos²θ → 0`, `cosθcos2θ → 1`).  The weighted
square-integrability of `u''` supplies the needed boundedness of `u'` near `0`, hence the
existence of the limit `lim_{0⁺} u` (`SourceBound.auxLimitAtZero`), and the assumed vanishing
of the moment then forces that limit to be `0` (`SourceBound.auxMoment`). -/
theorem wsSliceLeft {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ)
    (hL : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ)
    (hmom : (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) = 0) :
    Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨α, hα⟩ := SourceBound.auxLimitAtZero hsm h2
  have hm := SourceBound.auxMoment hsm h2 hL hα
  have hα0 : α = 0 := by
    have h1 : (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) = -α := hm
    rw [hmom] at h1
    linarith
  simpa [hα0] using hα

end Work.FTS.EllipticEst.remov
