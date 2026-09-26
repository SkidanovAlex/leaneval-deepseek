import Mathlib
import Submission.Work.Modular.Poisson.Periodize

namespace Work.Poisson

/-- The torus character `mFourier (-k)` evaluated at the projection of `x` coincides with the
Euclidean character `charFun` of the adjoint of `d` at `d.symm x`.

Both sides expand to `exp (-(2πi) * ∑ᵢ kᵢ xᵢ)`: the left-hand side is a product of the
`UnitAddCircle` characters `fourier (-kᵢ)`, and the right-hand side uses
`⟪d.symm x, adjoint d (intVecE k)⟫ = ⟪x, intVecE k⟫ = ∑ᵢ xᵢ kᵢ`. -/
theorem mFourier_eq_charFun_adjoint {n : ℕ}
    (d : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (k : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    UnitAddTorus.mFourier (-k)
        (Work.Modular.projTorus (EuclideanSpace.equiv (Fin n) ℝ x)) =
      Work.Modular.charFun (LinearMap.adjoint d.toLinearMap (Work.Modular.intVecE k))
        (d.symm x) := by
  have hL : UnitAddTorus.mFourier (-k)
        (Work.Modular.projTorus (EuclideanSpace.equiv (Fin n) ℝ x))
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
          ∑ i, (k i : ℂ) * ((EuclideanSpace.equiv (Fin n) ℝ x) i : ℂ)) := by
    rw [UnitAddTorus.mFourier]
    simp only [ContinuousMap.coe_mk, Work.Modular.projTorus_apply, fourier_coe_apply]
    rw [← Complex.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.neg_apply]
    push_cast
    ring
  have hR : Work.Modular.charFun
        (LinearMap.adjoint d.toLinearMap (Work.Modular.intVecE k)) (d.symm x)
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
          ∑ i, (k i : ℂ) * ((EuclideanSpace.equiv (Fin n) ℝ x) i : ℂ)) := by
    rw [Work.Modular.charFun]
    congr 1
    rw [LinearMap.adjoint_inner_right]
    simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply, Work.Modular.intVecE_apply]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (EuclideanSpace.equiv (Fin n) ℝ x) i = x.ofLp i from rfl]
    ring
  rw [hL, hR]

end Work.Poisson
