import Mathlib
import Submission.Work.NN.Core.DbarCnPertAux

/-!
# The inverse of `1 + X` is complex linear when `X` is

Let `X : ℂⁿ →L[ℝ] ℂⁿ` be a continuous `ℝ`-linear endomorphism of `ℂⁿ` which happens to be
`ℂ`-linear, i.e. `X (c • v) = c • X v` for all `c : ℂ`, `v : ℂⁿ`.  Then `1 + X` is also
`ℂ`-linear (the `ℝ`-linear identity map is `ℂ`-linear), so if `1 + X` is invertible as an
`ℝ`-linear map then its inverse is `ℂ`-linear as well: it is the inverse of a bijective
`ℂ`-linear map.

Indeed, `f := 1 + X` satisfies `f (c • w) = c • f w`, hence for `y := f.inverse v`
(the unique preimage of `v` under `f`) the vector `c • y` is the unique preimage of `c • v`:
`f (c • y) = c • f y = c • v`, and `f` is injective.

This is the step that lets one invert `1 + Bop A z` (a `ℂ`-linear operator on `ℂⁿ`) inside the
complex-linear Fredholm/perturbation calculus, and to interchange it with complex scalar
multiplication.
-/

namespace Work.NN.Core

/-- If `X` is `ℂ`-linear then so is `1 + X`. -/
lemma one_add_map_smul {n : ℕ} {X : Cn n →L[ℝ] Cn n}
    (hlin : ∀ (c : ℂ) (v : Cn n), X (c • v) = c • X v) (c : ℂ) (v : Cn n) :
    (1 + X) (c • v) = c • ((1 + X) v) := by
  simp only [add_apply, one_apply_eq_self, hlin c v, smul_add]

/-- The inverse of a `ℂ`-linear `ℝ`-linear automorphism of `ℂⁿ` is again `ℂ`-linear. -/
theorem inverse_one_add_map_smul {n : ℕ} {X : Cn n →L[ℝ] Cn n} (hX : (1 + X).IsInvertible)
    (hlin : ∀ (c : ℂ) (v : Cn n), X (c • v) = c • X v) (c : ℂ) (v : Cn n) :
    ContinuousLinearMap.inverse (1 + X) (c • v) = c • ContinuousLinearMap.inverse (1 + X) v := by
  have h2 : (1 + X) (ContinuousLinearMap.inverse (1 + X) (c • v)) = c • v :=
    hX.self_apply_inverse _
  have h3 : (1 + X) (c • ContinuousLinearMap.inverse (1 + X) v) = c • v := by
    rw [one_add_map_smul hlin c, hX.self_apply_inverse v]
  exact hX.injective (by rw [h2, h3])

end Work.NN.Core
