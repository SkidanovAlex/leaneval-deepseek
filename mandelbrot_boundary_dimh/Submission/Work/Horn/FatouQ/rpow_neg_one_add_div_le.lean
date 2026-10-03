import Mathlib

namespace Work.Horn.FatouQ

/-- For `a ≥ 1` the real power function `x ↦ a ^ x` is monotone; and for
`1 ≤ q` and `m ≤ q - 1` the exponent `-1 + m/q` is at most `-1/q`. -/
theorem rpow_neg_one_add_div_le {q m : ℕ} {a : ℝ} (hq : 1 ≤ q) (ha : 1 ≤ a) (hm : m ≤ q - 1) :
    a ^ (-(1 : ℝ) + (m : ℝ) / (q : ℝ)) ≤ a ^ (-(1 : ℝ) / (q : ℝ)) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hmR : (m:ℝ) ≤ (q:ℝ) - 1 := by
    have h : (m:ℝ) ≤ ((q - 1 : ℕ):ℝ) := by exact_mod_cast hm
    rw [Nat.cast_sub hq] at h
    push_cast at h
    linarith
  have hexp : -(1:ℝ) + (m:ℝ)/(q:ℝ) ≤ -(1:ℝ)/(q:ℝ) := by
    have h := div_le_div_of_nonneg_right hmR hqR.le
    rw [sub_div, div_self (ne_of_gt hqR)] at h
    rw [neg_div]
    linarith
  exact Real.rpow_le_rpow_of_exponent_le ha hexp

end Work.Horn.FatouQ
