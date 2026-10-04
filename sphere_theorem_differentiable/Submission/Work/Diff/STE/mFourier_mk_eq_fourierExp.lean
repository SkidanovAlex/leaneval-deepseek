import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

/-- Mathlib's `n`-th Fourier character on the additive unit torus, evaluated at the image of
`x : ι → ℝ` under the quotient map `ℝ → UnitAddCircle`, agrees with the exponential monomial
`fourierExp n x = exp (2πi ∑ᵢ nᵢ xᵢ)` used in the STE Sobolev/Fourier development. -/
theorem mFourier_mk_eq_fourierExp {ι : Type*} [Fintype ι] (n : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier n (fun i => (x i : UnitAddCircle)) = Work.Diff.STE.fourierExp n x := by
  simp only [Work.Diff.STE.fourierExp, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

end Work.Diff.STE
