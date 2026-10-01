import Mathlib

namespace Work.ZeroDensity.Ingham

theorem critTailTLeExp (A T : ℝ) (hA : 100 ≤ A) (hT : 2 ≤ T) :
    Real.sqrt T ≤ Real.exp ((A * Real.log (A * T)) / 100) ∧
      T ^ 4 ≤ Real.exp ((A * Real.log (A * T)) / 25) := by
  have hTpos : 0 < T := by linarith
  have hApos : 0 < A := by linarith
  have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogAT_ge : Real.log T ≤ Real.log (A * T) :=
    Real.log_le_log hTpos (by nlinarith)
  have hL_nonneg : 0 ≤ Real.log (A * T) := le_trans hlogT_nonneg hlogAT_ge
  constructor
  · have hx : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
    apply (Real.log_le_iff_le_exp hx).mp
    rw [Real.log_sqrt (le_of_lt hTpos)]
    nlinarith [hlogAT_ge, hL_nonneg, hA, hlogT_nonneg]
  · have hx4 : 0 < T ^ 4 := by positivity
    apply (Real.log_le_iff_le_exp hx4).mp
    rw [Real.log_pow]
    have hmain : 100 * Real.log T ≤ A * Real.log (A * T) := by
      have h1 : 100 * Real.log (A * T) ≤ A * Real.log (A * T) :=
        mul_le_mul_of_nonneg_right hA hL_nonneg
      linarith
    linarith

end Work.ZeroDensity.Ingham
