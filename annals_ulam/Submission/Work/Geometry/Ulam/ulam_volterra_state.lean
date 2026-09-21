import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Geometry.Ulam.AbelBeta

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped Interval

noncomputable section

/-- The four-coordinate state `(x, y, x', y')` used in the odd-case Volterra
reduction.  It is definitionally `ℝ⁴`, with the first two coordinates carrying
the chord endpoints and the last two the independent derivative unknowns. -/
abbrev UlamState : Type := Fin 4 → ℝ

/-- The two-coordinate state `(x, y)` used by the Abel-reduced kernels. -/
abbrev UlamState2 : Type := Fin 2 → ℝ

/-- The Abel normalisation constant
`∫₀¹ (√(τ(1-τ)))⁻¹ dτ`, which the paper denotes by `C`. -/
def ulamAbelConst : ℝ := ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹

/-- The Abel normalisation constant is `π`. -/
lemma ulamAbelConst_eq_pi : ulamAbelConst = Real.pi := by
  unfold ulamAbelConst
  -- This is the classical beta-integral value; the repository already has the
  -- named scalar computation as `integral_one_div_sqrt_tau_one_sub_tau_eq_pi`.
  simpa [one_div] using integral_one_div_sqrt_tau_one_sub_tau_eq_pi

end

end Commons.Geometry.Ulam
