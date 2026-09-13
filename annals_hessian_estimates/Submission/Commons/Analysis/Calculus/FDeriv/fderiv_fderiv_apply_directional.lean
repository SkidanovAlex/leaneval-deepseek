import Mathlib
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_directional_deriv

/-!
# The second directional derivative as an application of the second iterated derivative

For a `C²` function `u` on an open set `s`, the derivative at `x` in direction `z` of the
function `y ↦ (fderiv ℝ u y) w` is the second iterated derivative of `u` at `x` evaluated on the
pair `(z, w)`:

`fderiv ℝ (fun y => (fderiv ℝ u y) w) x z = (iteratedFDeriv ℝ 2 u x) ![z, w]`.

This is the `n = 1` case of the general currying identity
`Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_directional_deriv`, together with
`iteratedFDeriv_one_apply` which identifies `iteratedFDeriv ℝ 1 u y ![w]` with
`(fderiv ℝ u y) w`.
-/

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace in
theorem fderiv_fderiv_apply_directional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {s : Set E} {x z w : E} (hs : IsOpen s) (hx : x ∈ s)
    (hu : ContDiffOn ℝ 2 u s) :
    fderiv ℝ (fun y => (fderiv ℝ u y) w) x z = (iteratedFDeriv ℝ 2 u x) ![z, w] := by
  have h := iteratedFDeriv_directional_deriv (E := E) hs hx (n := 1) hu (![w] : Fin 1 → E) z
  simpa using h

end Commons.Analysis.Calculus.FDeriv
