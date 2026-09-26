import Mathlib
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.psi1_iteratedDeriv_bound
import Submission.Work.RadialSpace.iteratedDeriv_ofReal

namespace Work.Asymptotics

/-- The regularising factor `psi1` has uniformly bounded iterated derivatives.

`psi1 x = 2 ∫_0^1 (1-s) cos (s x) ds` is a parametric integral whose `j`-th derivative is the
integral of the `j`-th derivative of the integrand, and
`|∂_x^j (2(1-s)cos(sx))| ≤ 2(1-s)s^j ≤ 2` on `[0,1]`; hence every iterated derivative of `psi1`
is bounded by `2`.

The two analytic ingredients are already available in the workspace:

* `Work.Asymptotics.psi1_iteratedDeriv_bound` bounds the iterated derivatives of the
  complexification `psiC = fun x => ((psi1 x : ℝ) : ℂ)` by `2`;
* `Work.RadialSpace.iteratedDeriv_ofReal` identifies the iterated derivative of the
  complexification with the complexification of the iterated derivative. -/
theorem psi1_deriv_bounded (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, |iteratedDeriv j psi1 x| ≤ B := by
  refine ⟨2, by norm_num, fun x => ?_⟩
  have h := psi1_iteratedDeriv_bound j x
  rw [show psiC = (fun x : ℝ => ((psi1 x : ℝ) : ℂ)) from rfl] at h
  rw [Work.RadialSpace.iteratedDeriv_ofReal j psi1 x] at h
  rwa [Complex.norm_real, Real.norm_eq_abs] at h

end Work.Asymptotics
