/-
# The `t`-integral of a weighted family (helper vocabulary for the Case-B assembly of area A6)

`Work.KMTPlan.A6.mdlWInt` is the `t`-integral of a weighted frozen-`t` slice of the model
tuple.  The present module only records the *generic* form of that object,

  `mdlWIntF w Y n x = ∫_{1/2}^1 w n t * Y t n x dt`,

so that statements about it (e.g. `Work.KMTPlan.A6.MdlWIntNormLe`) can be written without the
interval-integral notation, which is scope-dependent (it needs `open scoped Interval` in the file
where the statement is elaborated).
-/
import Submission.Work.KMTPlan.A6.varNorm_integral_le

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory PointwiseErgodicTheorems
open scoped ENNReal NNReal BigOperators Interval

/-- **The `t`-integral of the weighted family** `(n,x) ↦ ∫_{1/2}^1 w n t * Y t n x dt`. -/
noncomputable def mdlWIntF (w : ℕ → ℝ → ℂ) (Y : ℝ → ℕ → ℤ → ℂ) : ℕ → ℤ → ℂ :=
  fun n x => ∫ t in (1 / 2 : ℝ)..1, w n t * Y t n x

end

end Work.KMTPlan.A6
