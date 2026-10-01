/-
# OffAxis/Lead/Tf72FcOneEqG72

The bridge `tf72Fc 1 = G72` (the Lemma 7.2 Laplace transform at `λ = 1` is the scale-free
transform `G72`) in the namespace `Work.ZeroFreeTables.OffAxis`, where
`OffAxis/Lead/Rect10_3OneRealEngine` needs it.

`ZeroFreeTables/OffAxis/HB10_3Num_core.lean` provides this statement too, but also imports the
`G72Cancel`/`G72LargeE2`/`G72DerivUpper`/`G72DerivMidSigma` numerical chain; the present module
gets it directly from `OffAxis/Tf72One/Core` instead, whose import closure is light.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.OffAxis.Tf72One.Core

namespace Work.ZeroFreeTables.OffAxis

/-- At `λ = 1` the Lemma 7.2 Laplace transform `tf72Fc` coincides with the scale-free transform
`G72`. -/
theorem tf72Fc_one_eq_G72 (z : ℂ) : tf72Fc 1 z = G72 z :=
  Work.OffAxis.Tf72One.tf72Fc_one_eq_G72 z

end Work.ZeroFreeTables.OffAxis
