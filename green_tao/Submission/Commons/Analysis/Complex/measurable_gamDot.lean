import Mathlib
import Submission.Commons.Analysis.Complex.contour_shift_residue

namespace Commons.Analysis.Complex

/-! ## Measurability of `PhiPos`, `PhiNeg`, `Phi'`, `gamDot`

`gamDot β` is defined as a derivative (`gamDot β y = Phi' β y + I`), and only
`aestronglyMeasurable_deriv` is available for it in general, i.e. an a.e. statement.
Here we simply observe that the definitional formula is a piecewise expression built
from continuous pieces and `Real.log`, hence plainly measurable. -/

/-- `PhiPos β y = β / ((y + 2) * (log (y + 2)) ^ 2)` is measurable. -/
lemma measurable_PhiPos (β : ℝ) : Measurable (PhiPos β) := by
  rw [show PhiPos β = fun y : ℝ => β / ((y + 2) * (Real.log (y + 2)) ^ 2) from rfl]
  measurability

/-- `PhiNeg β y = -(β / ((-y + 2) * (log (-y + 2)) ^ 2))` is measurable. -/
lemma measurable_PhiNeg (β : ℝ) : Measurable (PhiNeg β) := by
  rw [show PhiNeg β = fun y : ℝ => -(β / ((-y + 2) * (Real.log (-y + 2)) ^ 2)) from rfl]
  measurability

/-- The piecewise derivative `Phi' β` is measurable. -/
lemma measurable_Phi' (β : ℝ) : Measurable (Phi' β) := by
  rw [show Phi' β = fun y : ℝ => if 0 ≤ y then PhiPos β y else PhiNeg β y from rfl]
  exact Measurable.ite (measurableSet_le measurable_const measurable_id)
    (measurable_PhiPos β) (measurable_PhiNeg β)

/-- The curve velocity `gamDot β y = Phi' β y + I` is (not merely a.e.) measurable: it is a
piecewise formula built from continuous pieces and `Real.log`.

Proof (verified): unfold `gamDot`, `Phi'`; use `Measurable.ite` with
`measurableSet_le measurable_const measurable_id` for the side condition `0 ≤ y`; `PhiPos β` and
`PhiNeg β` are measurable because `Real.measurable_log` and `Measurable.div`/`pow_const`/
`add`/`neg` apply; finally `Complex.measurable_ofReal` and `Measurable.add` with the constant `I`.
This is useful because `gamDot` is defined as a derivative, and `aestronglyMeasurable_deriv` gives
only a.e. strong measurability, which cannot be lifted to the product measure without extra work. -/
theorem measurable_gamDot (β : ℝ) : Measurable (Commons.Analysis.Complex.gamDot β) := by
  rw [show gamDot β = fun y : ℝ => (Phi' β y : ℂ) + Complex.I from rfl]
  exact (Complex.measurable_ofReal.comp (measurable_Phi' β)).add measurable_const

end Commons.Analysis.Complex
