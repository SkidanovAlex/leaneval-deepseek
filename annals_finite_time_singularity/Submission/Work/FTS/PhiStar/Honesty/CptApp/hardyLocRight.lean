/-
# The right-end local angular Hardy inequality `hardyLocRight`

`Work.FTS.PhiStar.Honesty.CptApp.hardyLocRight`: for `1 < c ≤ 3/2`, `π/4 ≤ θ₁ < π/2` and `u` of
class `C¹` on `(θ₁, π/2)` whose right trace vanishes,

  `∫_{(θ₁,π/2)} sin(2θ)^{-c} u² ≤ 4/(c-1)² ∫_{(θ₁,π/2)} sin(2θ)^{2-c} (u')²`,

as an inequality of Lebesgue integrals in `ℝ≥0∞` (no integrability hypothesis is needed: the
left-hand side is finite as soon as the right-hand one is).

## Route

The reflection `φ ↦ π/2 - φ` is measure preserving (`Measure.measurePreserving_sub_left`), maps
`(0, π/2 - θ₁)` onto `(θ₁, π/2)`, satisfies `sin (2 (π/2 - φ)) = sin (2φ)` (`Real.sin_pi_sub`),
and turns `deriv` into `-deriv` (`deriv_comp_const_sub`).  It therefore transports both sides of
the inequality to the *left-end* problem on `(0, π/2 - θ₁)` for the reflected datum
`φ ↦ u (π/2 - φ)`, in the favourable range `0 < π/2 - θ₁ ≤ π/4` (from `π/4 ≤ θ₁ < π/2`).
That left-end problem is exactly `Work.FTS.PhiStar.Honesty.CptApp.hardyLoc` (the sub-interval
version of the sharp angular weighted Hardy inequality), whose constant is `4/(c-1)²`.

The transport of the two integrals together with the two hypotheses (`ContDiffOn` and the
vanishing right trace) is the delegated lemma
`Work.FTS.PhiStar.Honesty.CptApp.reflect_hardyLocRight`; the present file only assembles it with
`hardyLoc`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Defs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.hardyLoc
import Submission.Work.FTS.PhiStar.Honesty.CptApp.reflect_hardyLocRight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

theorem hardyLocRight (c θ₁ : ℝ) (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) (hθ : θ₁ < Real.pi / 2)
    (hθ2 : Real.pi / 4 ≤ θ₁) {u : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u (Set.Ioo θ₁ (Real.pi / 2)))
    (h1 : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    MeasureTheory.lintegral
        (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioo θ₁ (Real.pi / 2)))
        (fun θ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) *
        MeasureTheory.lintegral
          (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioo θ₁ (Real.pi / 2)))
          (fun θ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
  -- the reflected interval is a genuine left-end interval of length at most `π/4`
  have hX0 : 0 < Real.pi / 2 - θ₁ := by linarith
  have hX4 : Real.pi / 2 - θ₁ ≤ Real.pi / 4 := by linarith
  -- reflection: hypotheses for the left-end problem, and the two integral identities
  obtain ⟨hgsm, hgtend, hL, hR⟩ := reflect_hardyLocRight c θ₁ hθ hu h1
  rw [hL, hR]
  exact hardyLoc c (Real.pi / 2 - θ₁) hc1 hc2 hX0 hX4 hgsm hgtend

end Work.FTS.PhiStar.Honesty.CptApp
