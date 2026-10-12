import Mathlib.Analysis.Fourier.AddCircleMulti
import Submission.Work.BoseFixR.Rb5Lin.ps3_mFourier_apply
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.Rb5Lin

/-- The `ℂ`-scalar action of the torus Fourier monomial `mFourier (-n)` at a point lifted
from `ℝ³`: multiplying a scalar `z` by it gives `z * exp (-(2πi ∑ᵢ yᵢ nᵢ))`. -/
theorem ps3_mFourier_smul (n : Fin 3 → ℤ) (y : Fin 3 → ℝ) (z : ℂ) :
    UnitAddTorus.mFourier (-n) (fun i => ((y i : ℝ) : UnitAddCircle)) • z =
      z * Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((y i : ℂ) * (n i : ℂ))))) := by
  have hsum : (∑ i : Fin 3, (y i : ℂ) * ((-n) i : ℂ))
      = -(∑ i : Fin 3, (y i : ℂ) * (n i : ℂ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.neg_apply, Int.cast_neg, mul_neg]
  rw [ps3_mFourier_apply, smul_eq_mul, hsum, mul_neg]
  exact mul_comm _ _

end Work.BoseFixR.Rb5Lin
