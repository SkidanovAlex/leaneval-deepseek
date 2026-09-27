import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

open scoped Matrix

/-- The shearing `g ↦ u(r) g u(-r)` of EKL (e:As) agrees with its explicit
matrix formula `shearMat`.  This is a pure unfolding of the definitions
`shear = u r * g * u (-r)`, `u r = transvection h01 r` and
`shearMat M r = (1 + E₀₁ r) * M * (1 - E₀₁ r)`, together with the two Mathlib
facts `coe_mul` (the matrix coercion is multiplicative) and `transvection_coe`
(`transvection h b = 1 + single h b`). -/
theorem shear_coe (g : SL3) (r : ℝ) :
    ((shear g r : SL3) : Matrix (Fin 3) (Fin 3) ℝ) = shearMat (g : Matrix (Fin 3) (Fin 3) ℝ) r := by
  simp only [shear, u, uij, shearMat, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, sub_eq_add_neg, Matrix.single_neg]

end Work.EKLC8Core
