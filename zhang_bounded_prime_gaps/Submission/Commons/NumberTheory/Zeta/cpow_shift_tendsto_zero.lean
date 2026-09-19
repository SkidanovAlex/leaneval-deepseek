import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter

namespace Commons.NumberTheory.Zeta

theorem cpow_shift_tendsto_zero {w : ℂ} {N : ℕ} (hN : 1 ≤ N) (hw : w.re < 0) :
    Filter.Tendsto (fun m : ℕ => (((N + m : ℕ) : ℂ) ^ w)) Filter.atTop (nhds (0 : ℂ)) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let a : ℝ := -w.re
  have ha : 0 < a := neg_pos.mpr hw
  have hbase : Tendsto (fun m : ℕ => ((m : ℝ) + (N : ℝ))) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (N : ℝ) tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun m : ℕ => ((m : ℝ) + (N : ℝ)) ^ (-a)) atTop (nhds (0 : ℝ)) := by
    exact (tendsto_rpow_neg_atTop ha).comp hbase
  have harg : w.re = -a := by simp [a]
  have hlim2 : Tendsto (fun m : ℕ => ((m : ℝ) + (N : ℝ)) ^ w.re) atTop (nhds (0 : ℝ)) := by
    simpa [harg] using hlim
  convert hlim2 using 1
  funext m
  have hpos : 0 < N + m := by
    exact lt_of_lt_of_le zero_lt_one (Nat.le_trans hN (Nat.le_add_right N m))
  rw [Complex.norm_natCast_cpow_of_pos hpos w]
  rw [Nat.cast_add]
  rw [add_comm]

end Commons.NumberTheory.Zeta