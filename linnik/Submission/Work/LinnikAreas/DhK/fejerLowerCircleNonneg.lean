import Mathlib
import Submission.Work.LinnikAreas.DhK.TuranDefs
import Submission.Work.LinnikAreas.turanFejerComplex

/-!
# Lower bound for `fejerQ` off the unit circle

`fejerQ J z = Σ_{j=1}^{J} (1 - j/(J+1)) Re(z^j)`.  The hypothesis that the Fejér kernel is
non-negative on the unit circle (`0 ≤ 1 + 2 fejerQ J ζ` for `‖ζ‖ = 1`) yields, by the sharp
harmonic (Poisson) bound for the harmonic extension of a non-negative trigonometric polynomial,
the estimate `fejerQ J z ≥ -‖z‖/(1+‖z‖)` throughout the closed unit disc.

The analytic content here is the classical Fejér-kernel lower bound, already available as
`Work.LinnikAreas.turanFejerComplex` (which does not use the circle hypothesis `h` at all: the
bound holds unconditionally, since `1 + 2 fejerQ J ζ ≥ 0` on the circle is itself a theorem).
-/

namespace Work.LinnikAreas.DhK

theorem fejerLowerCircleNonneg (J : ℕ)
    (h : ∀ ζ : ℂ, ‖ζ‖ = 1 → 0 ≤ 1 + 2 * fejerQ J ζ)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    -(‖z‖ / (1 + ‖z‖)) ≤ fejerQ J z := by
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · subst hJ
    have hz0 : fejerQ 0 z = 0 := by
      simp only [fejerQ, fejerW]
      rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) by decide]
      simp
    rw [hz0]
    have hnonneg : 0 ≤ ‖z‖ / (1 + ‖z‖) := by positivity
    linarith
  · simpa only [fejerQ, fejerW, neg_div] using
      Work.LinnikAreas.turanFejerComplex J hJ z hz

end Work.LinnikAreas.DhK
