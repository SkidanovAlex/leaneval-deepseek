import Mathlib
import Submission.Work.LinnikAreas.Setup
import Submission.Work.LinnikAreas.PrincipalZeroCount
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Ingham.inghamArithmetic
import Submission.Work.ZeroDensity.Zeta.ZetaZeroDefs
import Submission.Work.ZeroDensity.Ingham.assembly
import Submission.Work.ZeroDensity.Ingham.zetaSeparatedReduction
import Submission.Work.ZeroDensity.Ingham.zetaCountCombined
import Submission.Work.ZeroDensity.Ingham.zetaCountCombinedClean

namespace Work.ZeroDensity.Montgomery

open scoped Classical BigOperators

/-- **Ingham's zero-density estimate for the Riemann zeta function** (Ingham 1937; Titchmarsh,
*The Theory of the Riemann Zeta-Function*, Chapter IX; Iwaniec–Kowalski §10.1): for every
`ε > 0` there is `C > 0` such that for `1/2 ≤ σ ≤ 1` and `T ≥ 1` the multiplicity-weighted
number of non-trivial zeros `ρ` of `ζ` with `σ ≤ Re ρ ≤ 1` and `|Im ρ| ≤ T` is at most
`C · T^{3(1-σ)/(2-σ)+ε}`.

This is the *single* `L`-function (`ζ`) case of the zero-density problem; the proof runs through
the approximate functional equation for `ζ` (which produces a Dirichlet polynomial of length
`≍ √(T(1+|t|))`), the fourth moment `∫_0^T |ζ(1/2+it)|^4 dt ≪ T log^4 T` and the large-values
(large sieve) machinery, with no character sums involved. -/
theorem inGhamZetaDensity : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (σ T : ℝ), (1 : ℝ) / 2 ≤ σ → σ ≤ 1 → 1 ≤ T →
      (∑ᶠ ρ : ℂ, (if analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
        then (analyticOrderNatAt completedRiemannZeta ρ : ℝ) else 0))
        ≤ C * T ^ (3 * (1 - σ) / (2 - σ) + ε) :=
  -- Montgomery-Vaughan §28.4.1 at `q = Q = 1`, assembled from the separated-set reduction and
  -- the combined large-values count (both in `Submission/Work/ZeroDensity/Ingham/`).
  --
  -- The combined count is produced here from the *wide* Ingham/Montgomery detector: its two
  -- inputs are the critical-line tail estimate `zetaDetectorBig.critTailSmallBig` and the
  -- contour-integral count `zetaDetectorBig.zetaIntegralCountWide`.
  Work.ZeroDensity.Ingham.inGhamZetaDensity_of_pieces
    Work.ZeroDensity.Ingham.zetaSeparatedReduction
    (fun A hA =>
      Work.ZeroDensity.Ingham.zetaCountCombinedClean_of_pieces A hA
        Work.ZeroDensity.Ingham.zetaDetectorBig.critTailSmallBig
        Work.ZeroDensity.Ingham.zetaDetectorBig.zetaIntegralCountWide)

end Work.ZeroDensity.Montgomery
