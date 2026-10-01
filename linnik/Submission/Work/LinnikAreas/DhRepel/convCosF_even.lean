import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l71cond

open MeasureTheory

namespace Work.LinnikAreas.DhRepel

/-- The convolution square of Heath-Brown's `extCosG` is even in the displacement: substituting
`s ↦ -s` (available because Lebesgue measure on `ℝ` is negation-invariant) and using that
`extCosG` is even. -/
theorem convCosF_even {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) (v : ℝ) :
    (∫ s : ℝ, Commons.NumberTheory.Linnik.extCosG θ lam s * Commons.NumberTheory.Linnik.extCosG θ lam (-v - s))
      = (∫ s : ℝ, Commons.NumberTheory.Linnik.extCosG θ lam s * Commons.NumberTheory.Linnik.extCosG θ lam (v - s)) := by
  rw [← integral_neg_eq_self (f := fun s => Commons.NumberTheory.Linnik.extCosG θ lam s * Commons.NumberTheory.Linnik.extCosG θ lam (-v - s))]
  apply integral_congr_ae
  filter_upwards with s
  rw [Commons.NumberTheory.Linnik.extCosG_even]
  have : -v - -s = -(v - s) := by ring
  rw [this, Commons.NumberTheory.Linnik.extCosG_even]

end Work.LinnikAreas.DhRepel
