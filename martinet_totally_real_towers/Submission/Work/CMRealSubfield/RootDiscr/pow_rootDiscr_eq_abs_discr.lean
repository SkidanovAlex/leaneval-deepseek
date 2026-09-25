import Mathlib

open NumberField

namespace Work.CMRealSubfield.RootDiscr

theorem pow_rootDiscr_eq_abs_discr (K : Type*) [Field K] [NumberField K] :
    NumberField.rootDiscr K ^ Module.finrank ℚ K = |(NumberField.discr K : ℝ)| := by
  rw [NumberField.rootDiscr_def, Int.cast_abs]
  exact Real.rpow_inv_natCast_pow (abs_nonneg _) (Module.finrank_pos (R := ℚ) (M := K)).ne'

end Work.CMRealSubfield.RootDiscr
