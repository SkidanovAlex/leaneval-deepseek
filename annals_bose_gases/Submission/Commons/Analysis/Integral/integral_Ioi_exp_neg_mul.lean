import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Integral

open MeasureTheory

/-- `∫_{t>0} exp (-(lam * t)) dt = lam⁻¹` for `lam > 0`. -/
theorem integral_Ioi_exp_neg_mul {lam : ℝ} (hlam : 0 < lam) :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(lam * t))) = lam⁻¹ := by
  simpa using integral_exp_mul_Ioi (a := -lam) (c := 0) (by linarith)

end Commons.Analysis.Integral