import Mathlib

namespace Work.Fx

/-- For `b > 0` the remainder of the truncating division of `a` by `b` has modulus `< b`. -/
private theorem abs_tmod_lt (a b : ℤ) (hb : 0 < b) : |a.tmod b| < b :=
  abs_lt.mpr ⟨Int.lt_tmod_of_pos a hb, Int.tmod_lt_of_pos a hb⟩

/-- `Int.tdiv` is rounding-towards-zero: its real value differs from the true quotient by
less than `1` when the divisor is positive.  (The statement asks for `≤ 1`.) -/
theorem FxTdivReal (a b : ℤ) (hb : 0 < b) :
    |(a.tdiv b : ℝ) - (a : ℝ) / (b : ℝ)| ≤ 1 ∧ (|a| < b → a.tdiv b = 0) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  constructor
  · -- Write `a = b * (a.tdiv b) + a.tmod b` and bound the remainder.
    have hcast : ((a.tmod b + a.tdiv b * b : ℤ) : ℝ) = (a : ℝ) := by
      rw [Int.tmod_add_tdiv_mul]
    push_cast at hcast
    have hkey : (a.tdiv b : ℝ) - (a : ℝ) / (b : ℝ) = -((a.tmod b : ℝ) / (b : ℝ)) := by
      field_simp
      linarith [hcast]
    rw [hkey, abs_neg, abs_div, abs_of_pos hbR, div_le_one hbR]
    have h := abs_tmod_lt a b hb
    exact_mod_cast le_of_lt h
  · -- If `|a| < b` then the quotient is `0`; handle the sign of `a` separately.
    intro h
    have ha1 : -b < a := (abs_lt.mp h).1
    have ha2 : a < b := (abs_lt.mp h).2
    by_cases h0 : 0 ≤ a
    · exact Int.tdiv_eq_zero_of_lt h0 ha2
    · have hneg : 0 < -a := neg_pos.mpr (not_le.mp h0)
      have hltb : -a < b := by omega
      have hz : (-a).tdiv b = 0 := Int.tdiv_eq_zero_of_lt (le_of_lt hneg) hltb
      have hnt : (-a).tdiv b = -(a.tdiv b) := Int.neg_tdiv a b
      omega

end Work.Fx
