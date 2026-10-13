import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoZeroOfMoment
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Honest.HonSliceLimitZero
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Endpt

/-!
# The endpoint moment identity `∫_{Iθ} (Lzero1 u) · sin θ cos²θ = -lim_{0⁺} u`

`Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u` is the angular operator of the elliptic section and
`φ = sin θ cos²θ` lies in the kernel of its formal adjoint (`Work.Elliptic.LzeroAdj_sinCos2`).
The function

  `Φ θ = -u'(θ) · sinθcos²θ + u(θ) · cos θ cos 2θ`

is a primitive of `(Lzero1 u) · φ` on `(0, π/2)` (`Work.Elliptic.hasDerivAt_Lzero_antideriv`),
so the fundamental theorem of calculus on `0..π/2` identifies the integral with the boundary
values of `Φ`: it vanishes at `π/2` (both `sinθcos²θ` and `cos θ cos 2θ` vanish there) and
equals `lim_{0⁺} u` at `0⁺` (`|sinθcos²θ| ≤ θ` kills the term carrying `u'`, while
`cos θ cos 2θ → 1` leaves `u(0⁺)`).

Two ingredients make the FTC legitimate under the present hypotheses, and both are available in
the workspace:

* `Work.FTS.EllipticEst.Honest.sliceMoment_eq_neg_limit` carries out the FTC and the evaluation
  of both boundary terms, assuming only that `u` is bounded with bounded derivative;
* `Work.FTS.EllipticEst.remov.abs_le_of_sq_mul_sEta` supplies that boundedness from the
  hypothesis `h2`: since `sEta θ = sin(2θ)^{-η} ≥ 1` on `(0, π/2)`, `h2` first yields
  `u'' ∈ L¹((0,π/2))`, hence `u'` is bounded by the fundamental theorem of calculus, and one
  further integration bounds `u` itself.

So the only hypothesis the present statement adds to the moment identity is the existence of the
left endpoint limit `u → α`, and the integral is `-α`. -/

theorem Lzero1_integral_eq_neg_limit {u : ℝ → ℝ} {α : ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ)
    (hL : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hlim : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds α)) :
    (∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) = -α := by
  -- `h2` bounds `u` and `deriv u` on the open interval (through `u'' ∈ L¹`)
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.remov.abs_le_of_sq_mul_sEta hu h2
  -- the moment identity then evaluates the integral as minus the left endpoint limit
  exact Work.FTS.EllipticEst.Honest.sliceMoment_eq_neg_limit hCpos.le hu
    (fun θ hθ => ⟨(hC θ hθ).2, (hC θ hθ).1⟩) hL hlim

end Work.FTS.EllipticEst.Endpt
