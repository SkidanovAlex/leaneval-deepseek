import Mathlib

namespace Work.CRed

lemma log_neg_int (m : ℤ) (hm : m ≤ -2) :
    Real.log (1 + 1 / (((-m - 1).toNat : ℕ) : ℝ)) = -Real.log (1 + 1 / (m : ℝ)) := by
  have htoNat : (((-m - 1).toNat : ℕ) : ℝ) = (-m : ℝ) - 1 := by
    have h : 0 ≤ -m - 1 := by omega
    have h2 : ((-m - 1).toNat : ℤ) = -m - 1 := Int.toNat_of_nonneg h
    exact_mod_cast h2
  rw [htoNat]
  have hm' : (m : ℝ) ≤ -2 := by exact_mod_cast hm
  have hd1 : (-m : ℝ) - 1 ≠ 0 := by linarith
  have hd2 : (m : ℝ) ≠ 0 := by linarith
  have hd3 : (m : ℝ) + 1 ≠ 0 := by linarith
  have harg : 1 + 1 / ((-m : ℝ) - 1) = (1 + 1 / (m : ℝ))⁻¹ := by
    field_simp
    ring
  rw [harg, Real.log_inv]

end Work.CRed
