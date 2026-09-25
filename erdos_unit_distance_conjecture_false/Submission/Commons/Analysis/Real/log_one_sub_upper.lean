import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.Real

theorem log_one_sub_upper {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Real.log (1 - u) ≤ -u := by
  have _hhu0 : 0 ≤ u := hu0
  rw [Real.log_le_iff_le_exp (sub_pos.mpr hu1)]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (Real.add_one_le_exp (-u) : (-u : ℝ) + 1 ≤ Real.exp (-u))

end Commons.Analysis.Real