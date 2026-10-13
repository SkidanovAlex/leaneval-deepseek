import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.sliceCSWeightedOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.WeakMoment.Open

/-- The weighted Cauchy–Schwarz bound for the second derivative `D2 u = u''` on the angular
slice `Iθ = [0, π/2]`, with the *explicit* constant `π/2`:

  `(∫_{Iθ} |u''|)² ≤ (∫_{Iθ} (u'')² sin(2θ)^{-η}) · (π/2)`.

Mathematics.  The Cauch–Schwarz step is the already-proved `sliceCSWeightedOpen`, which
needs only continuity of `u''` on the *open* interval:

  `(∫_{Iθ} |u''|)² ≤ (∫_{Iθ} (u'')² sin(2θ)^{-η}) · (∫_{Iθ} sin(2θ)^{η})`.

For the last factor, `θ ↦ sin(2θ)^η` is bounded by `1` on `Iθ` (since `0 ≤ sin(2θ) ≤ 1` there
and `η ≥ 0`), while `volume Iθ = π/2`; this is exactly the second component of
`Work.FTS.EllipticEst.integrableOn_sin_two_rpow` at `p = η`.

For the continuity input, `hsm 3` gives `ContDiffOn ℝ 3 u (Ioo 0 (π/2))`, and two applications
of `ContDiffOn.deriv_of_isOpen` (which requires the set to be open and the order to drop by at
most one) exhibit `u''` as `C¹`, hence continuous, on `(0, π/2)` (the endpoints of `Iθ` are a
null set and play no role in the slice integral). -/
theorem D2CsBound {u : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u θ|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) * (Real.pi / 2) := by
  -- `u''` is continuous on the *open* angular interval, from the hypothesis `hsm`.
  have hD2 : ContinuousOn (Work.FTS.EllipticEst.TT.D2 u)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h3 : ContDiffOn ℝ 3 u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hsm 3
    have h2 : ContDiffOn ℝ 2 (fun t => deriv u t) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      simpa only using h3.deriv_of_isOpen isOpen_Ioo (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
    have h1 : ContDiffOn ℝ 1 (fun θ => deriv (fun t => deriv u t) θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      simpa only using h2.deriv_of_isOpen isOpen_Ioo (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact h1.continuousOn
  -- The weighted Cauchy–Schwarz inequality of `sliceCSWeightedOpen`.
  have hcs := Work.FTS.EllipticEst.sliceCSWeightedOpen hD2 h
  -- The remaining factor is at most the length `π/2` of `Iθ`.
  have hle : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) ≤ Real.pi / 2 :=
    (Work.FTS.EllipticEst.integrableOn_sin_two_rpow Work.Spaces.eta_nonneg).2
  -- The weighted energy is nonnegative, so the right factor may be enlarged.
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.TT.sEta_nonneg hθ))
  calc (∫ θ in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u θ|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := hcs
    _ ≤ (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_left hle hnn

end Work.FTS.EllipticEst.WeakMoment.Open
