import Mathlib
import Submission.Work.MotAS.AzDefs
import Submission.Work.MotAS.AzDiscSubst

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3

/-- **The discriminant of the `X₀`-quadratic `azQ` is not a square**, over an arbitrary field `K` of
characteristic `5`: with `azA a b = a² − ab − b² ≠ 0` and any class `g ≠ 0`, the polynomial
`azDisc a b g = azC1 a b g ^ 2 - 4 * azC2 a b * azC0 a b g ∈ K[X₀,X₁]`
(definitions in `Submission/Work/MotAS/AzDefs.lean`) is not a square.

This is the `K`-generic form of the two PROVED source results
`Work.MotV5.ASLocal.azDisc_not_square_of_B_ne`
(`Submission/Work/MotV5/ASLocal/azDisc_not_square_of_B_ne.lean`, 413 lines) and
`Work.MotAS.AzDisc.azDisc_not_square_of_B_eq`
(`Submission/Work/MotAS/AzDisc/azDisc_not_square_of_B_eq.lean`, 283 lines), which cover the two cases
`azB a b ≠ 0` and `azB a b = 0` respectively over the base field `RatFunc 𝕜` with class
`Work.MotV.fAS 𝕜`.  In *both* source files every auxiliary definition and auxiliary result is already
stated for an arbitrary field `K` of characteristic `5`: only the final conclusion has the hardwired
`algebraMap 𝕜 (RatFunc 𝕜) _` / `Work.MotV.fAS 𝕜` and derives `fAS 𝕜 ≠ 0` internally.  The port is
therefore: copy both files, delete their private `fAS_ne_zero`, and replace their two final
conclusions by the single statement below, splitting on `azB a b = 0`.

The proof is the (already committed) generic argument
`Work.MotAS.AzDiscSubst.azDisc_not_square`: the substitution `X₁ ↦ X`, `X₂ ↦ X²` turns
`azDisc a b g` into a univariate polynomial with `natDegree = 7` (the coefficient of `X⁸` is
`−320·a²b²·B·A = 0` in characteristic `5`, that of `X⁷` is `−128·g·A⁴ ≠ 0`), whereas a square has
even `natDegree`; no case distinction on `azB a b` is needed.  -/
theorem azDisc_not_square (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hA : Work.MotAS.azA a b ≠ 0) (hg : g ≠ 0) :
    ∀ s : MvPolynomial (Fin 2) K, Work.MotAS.azDisc a b g ≠ s ^ 2 :=
  Work.MotAS.AzDiscSubst.azDisc_not_square K a b g hA hg

end Work.MotC5N3
