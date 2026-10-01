import Mathlib

namespace Work.LinnikBurgess

lemma sqrt_mul_sum_le {q H : ℕ} :
    Real.sqrt (q : ℝ) * ((H : ℝ) ^ 6 + (H : ℝ) ^ 5 * (q : ℝ) ^ ((1 : ℝ) / 6))
      ≤ 2 * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ)) := by
  by_cases hq : q = 0
  · subst hq
    simp [Real.sqrt_zero]
  by_cases hH : H = 0
  · subst hH
    simp
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hHpos : (0:ℝ) < (H:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hH
  set x : ℝ := (q:ℝ) ^ ((1:ℝ)/6) with hxdef
  have hxpos : 0 < x := by
    rw [hxdef]
    exact Real.rpow_pos_of_pos hqpos _
  have hxnonneg : 0 ≤ x := le_of_lt hxpos
  have hx3 : x ^ 3 = Real.sqrt (q:ℝ) := by
    rw [Real.sqrt_eq_rpow, hxdef, ← Real.rpow_natCast ((q:ℝ) ^ ((1:ℝ)/6)) 3]
    rw [← Real.rpow_mul (le_of_lt hqpos)]
    norm_num
  have hx6 : x ^ 6 = (q:ℝ) := by
    rw [hxdef, ← Real.rpow_natCast ((q:ℝ) ^ ((1:ℝ)/6)) 6]
    rw [← Real.rpow_mul (le_of_lt hqpos)]
    norm_num
  have hamgm : 3 * (H:ℝ)^2 * x ≤ 2 * (H:ℝ)^3 + x^3 := by
    have h1 : 0 ≤ ((H:ℝ) - x)^2 := sq_nonneg _
    have h2 : 0 ≤ 2*(H:ℝ) + x := by linarith
    have h3 : 0 ≤ ((H:ℝ) - x)^2 * (2*(H:ℝ) + x) := mul_nonneg h1 h2
    have hfac : 2*(H:ℝ)^3 - 3*(H:ℝ)^2*x + x^3 = ((H:ℝ) - x)^2 * (2*(H:ℝ) + x) := by ring
    linarith
  have hkey : (H:ℝ)^2 * x ≤ (H:ℝ)^3 + 2*x^3 := by
    nlinarith [hamgm, pow_nonneg (le_of_lt hHpos) 3, pow_nonneg hxnonneg 3]
  rw [← hx3, ← hx6]
  have hid : 2*(x^6 * (H:ℝ)^3 + (H:ℝ)^6 * x^3) - x^3 * ((H:ℝ)^6 + (H:ℝ)^5 * x)
      = (H:ℝ)^3 * x^3 * ((H:ℝ)^3 + 2*x^3 - (H:ℝ)^2*x) := by ring
  have hnn : 0 ≤ (H:ℝ)^3 * x^3 * ((H:ℝ)^3 + 2*x^3 - (H:ℝ)^2*x) := by
    apply mul_nonneg
    · exact mul_nonneg (pow_nonneg (le_of_lt hHpos) 3) (pow_nonneg hxnonneg 3)
    · nlinarith [hkey]
  linarith [hid, hnn]

end Work.LinnikBurgess
