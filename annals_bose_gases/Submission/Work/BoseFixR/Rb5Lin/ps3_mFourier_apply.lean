import Mathlib.Analysis.Fourier.AddCircleMulti
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.Rb5Lin

/-- `UnitAddTorus.mFourier` is by definition the product of the one-variable Fourier
monomials, so at a point lifted from `ℝ³` it is the exponential of `2πi ∑ᵢ yᵢ nᵢ`. -/
theorem ps3_mFourier_apply (n : Fin 3 → ℤ) (y : Fin 3 → ℝ) :
    UnitAddTorus.mFourier n (fun i => ((y i : ℝ) : UnitAddCircle)) =
      Complex.exp (2 * Real.pi * Complex.I * (∑ i, ((y i : ℂ) * (n i : ℂ)))) := by
  have hprod : UnitAddTorus.mFourier n (fun i => (y i : UnitAddCircle))
      = ∏ i : Fin 3, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n i : ℂ) * (y i : ℂ)) := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [fourier_coe_apply]
    norm_num
  rw [hprod, ← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

end Work.BoseFixR.Rb5Lin
