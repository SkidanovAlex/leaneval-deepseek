import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.I1SliceIBP
import Submission.Work.EllipticEst.Core.i0Aux.hardySigmaBoundaryCore
import Submission.Work.FTS.EllipticEst.AngAWeak.sliceSecondNonpos

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.RopGen

/-!
## `sliceSecNonposBochner` — the Bochner-integral form of the slice dichotomy

The 1-D slice dichotomy `∫ sin(2θ)^{-η} f f'' ≤ 0` is available in the workspace as
`Work.FTS.EllipticEst.AngAWeak.sliceSecondNonpos`, but *with* the extra hypothesis that the
integrand be integrable and with the integral taken over the open interval `Ioo 0 (π/2)`.
The statement requested here is the Bochner-integral form: no integrability hypothesis, and the
integral runs over `Work.Spaces.Iθ = Icc 0 (π/2)`.

The gap is closed by `MeasureTheory.integral_undef`: in Mathlib the Bochner integral of a
non-integrable function is `0`, so the non-integrable case is trivial; in the integrable case
the two `σ`-functions agree definitionally (`AngSecond.sig θ = sin(2θ)^{-η}`) and `Icc 0 (π/2)`
differs from `Ioo 0 (π/2)` by a null set.
-/

/-- The set integral over `Iθ = Icc 0 (π/2)` agrees with the set integral over `Ioo 0 (π/2)`
(the two sets differ by the two endpoints, a null set). -/
theorem setIntegral_Iθ_eq_Ioo (F : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, F θ) = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), F θ := by
  refine MeasureTheory.setIntegral_congr_set ?_
  rw [Work.Spaces.Iθ]
  exact MeasureTheory.Ioo_ae_eq_Icc.symm

/-- `IntegrableOn` is insensitive to replacing `Iθ = Icc 0 (π/2)` by `Ioo 0 (π/2)`. -/
theorem integrableOn_Iθ_iff_Ioo (F : ℝ → ℝ) :
    MeasureTheory.IntegrableOn F Work.Spaces.Iθ ↔
      MeasureTheory.IntegrableOn F (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have h1 : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[MeasureTheory.volume] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc
  rw [MeasureTheory.IntegrableOn, MeasureTheory.IntegrableOn,
    MeasureTheory.Measure.restrict_congr_set h1]

/-- **The slice dichotomy in Bochner form**: `∫_{Iθ} sin(2θ)^{-η} f f'' ≤ 0` for every `f` of
class `C²` on `(0, π/2)` whose one-sided limits at `0` and `π/2` are `0` (no integrability
hypothesis: if the integrand is not integrable the Bochner integral is `0`). -/
theorem sliceSecNonposBochner {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hπ : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (f θ * deriv (deriv f) θ)) ≤ 0 := by
  by_cases hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (f θ * deriv (deriv f) θ))
      Work.Spaces.Iθ
  · -- integrable case: reduce to the open interval and invoke the workspace dichotomy
    have hint2 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (f θ * deriv (deriv f) θ))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := (integrableOn_Iθ_iff_Ioo _).mp hint
    have hkey : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          Work.FTS.EllipticEst.AngSecond.sig θ * (f θ * deriv (deriv f) θ)) ≤ 0 :=
      Work.FTS.EllipticEst.AngAWeak.sliceSecondNonpos (f := f) hf h0 hπ
        (by simpa only [Work.FTS.EllipticEst.AngSecond.sig] using hint2)
    rw [setIntegral_Iθ_eq_Ioo]
    simpa only [Work.FTS.EllipticEst.AngSecond.sig] using hkey
  · -- non-integrable case: the Bochner integral is `0`
    have hni : ¬ MeasureTheory.Integrable
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (f θ * deriv (deriv f) θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      simpa only [MeasureTheory.IntegrableOn] using hint
    rw [MeasureTheory.integral_undef hni]

end Work.FTS.ClassC.RopGen
