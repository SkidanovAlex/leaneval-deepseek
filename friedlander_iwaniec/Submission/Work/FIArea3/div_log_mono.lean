import Mathlib

namespace Work.FIArea3

/-- A crude but sufficient lower bound for `Real.log 3`: it is at least `100/99`.
Indeed `log 3 = log 2 + log (3/2)`, `log 2 > 0.693` and `log (3/2) ≥ 1 - 2/3 = 1/3`. -/
lemma log_three_ge_100_99 : (100 / 99 : ℝ) ≤ Real.log 3 := by
  have h32 : (1 : ℝ) - (3 / 2 : ℝ)⁻¹ ≤ Real.log (3 / 2) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have h32' : (1 : ℝ) - (3 / 2 : ℝ)⁻¹ = 1 / 3 := by norm_num
  rw [h32'] at h32
  have hmul : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    have h := Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) (show (3 / 2 : ℝ) ≠ 0 by norm_num)
    rw [show (2 : ℝ) * (3 / 2) = 3 by norm_num] at h
    linarith
  rw [hmul]
  linarith [Real.log_two_gt_d9]

/-- `Real.log (Real.log 3) ≥ 1/100`, obtained by monotonicity from `log 3 ≥ 100/99`
together with `log x ≥ 1 - 1/x`. -/
lemma log_log_three_ge : (1 / 100 : ℝ) ≤ Real.log (Real.log 3) := by
  have h1 : (0 : ℝ) < 100 / 99 := by norm_num
  have hle : (100 / 99 : ℝ) ≤ Real.log 3 := log_three_ge_100_99
  have hmono : Real.log (100 / 99) ≤ Real.log (Real.log 3) := Real.log_le_log h1 hle
  have h2 : (1 / 100 : ℝ) ≤ Real.log (100 / 99) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 100 / 99 by norm_num)
    rw [show (100 / 99 : ℝ)⁻¹ = 99 / 100 by norm_num] at h
    linarith
  linarith

/-- `x ↦ x / log x` is dominated by its value at the right endpoint of a huge range: if
`log 3 ≤ t ≤ w+1` and `w ≥ 3.7·10^7` then `t/log t ≤ (w+1)/log(w+1)`.  For `e ≤ t` the claim
follows from `Real.log_div_self_antitoneOn` (`log x / x` antitone on `[e,∞)`); for
`log 3 ≤ t ≤ e` bound `t/log t ≤ e/log(log 3) ≈ 28.9` while `(w+1)/log(w+1) ≥ 2.1·10^6`. -/
theorem div_log_mono (t w : ℝ) (ht : Real.log 3 ≤ t) (htw : t ≤ w + 1)
    (hw : (37000000 : ℝ) ≤ w) :
    t / Real.log t ≤ (w + 1) / Real.log (w + 1) := by
  -- basic positivity facts
  have hlog3_gt1 : (1 : ℝ) < Real.log 3 := by
    have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    rwa [Real.log_exp] at h
  have hlog3pos : (0 : ℝ) < Real.log 3 := lt_trans one_pos hlog3_gt1
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le hlog3pos ht
  have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hlog3_gt1 ht
  have hlogtpos : (0 : ℝ) < Real.log t := Real.log_pos ht1
  have hw1pos : (0 : ℝ) < w + 1 := by linarith
  have hlogw1pos : (0 : ℝ) < Real.log (w + 1) := Real.log_pos (by linarith)
  by_cases hte : Real.exp 1 ≤ t
  · -- Case `e ≤ t`: `log x / x` is antitone on `[e, ∞)`.
    have hex : t ∈ Set.Ici (Real.exp 1) := hte
    have hey : w + 1 ∈ Set.Ici (Real.exp 1) := le_trans hte htw
    have hanti : Real.log (w + 1) / (w + 1) ≤ Real.log t / t :=
      Real.log_div_self_antitoneOn hex hey htw
    have hanti' : Real.log (w + 1) * t ≤ Real.log t * (w + 1) :=
      (div_le_div_iff₀ hw1pos htpos).mp hanti
    rw [div_le_div_iff₀ hlogtpos hlogw1pos]
    linarith
  · -- Case `t < e`: `t / log t` is small, `(w+1)/log(w+1)` is huge.
    rw [not_le] at hte
    have ht_le_e : t ≤ Real.exp 1 := le_of_lt hte
    have hloglog3 : (1 / 100 : ℝ) ≤ Real.log (Real.log 3) := log_log_three_ge
    have hloglog3pos : (0 : ℝ) < Real.log (Real.log 3) :=
      lt_of_lt_of_le (by norm_num) hloglog3
    have hlogt_ge : Real.log (Real.log 3) ≤ Real.log t := Real.log_le_log hlog3pos ht
    -- upper bound for `t / log t`
    have hbound1 : t / Real.log t ≤ 3000 := by
      have hstep : t / Real.log t ≤ Real.exp 1 / Real.log (Real.log 3) := by
        rw [div_le_div_iff₀ hlogtpos hloglog3pos]
        have h1 : t * Real.log (Real.log 3) ≤ Real.exp 1 * Real.log (Real.log 3) :=
          mul_le_mul_of_nonneg_right ht_le_e (le_of_lt hloglog3pos)
        have h2 : Real.exp 1 * Real.log (Real.log 3) ≤ Real.exp 1 * Real.log t :=
          mul_le_mul_of_nonneg_left hlogt_ge (le_of_lt (Real.exp_pos 1))
        linarith
      have hfac : Real.exp 1 / Real.log (Real.log 3) ≤ 3000 := by
        rw [div_le_iff₀ hloglog3pos]
        linarith [hloglog3, Real.exp_one_lt_three]
      linarith
    -- lower bound for `(w+1) / log (w+1)`
    have hbound2 : (3000 : ℝ) ≤ (w + 1) / Real.log (w + 1) := by
      have hlog_le : Real.log (w + 1) ≤ 2 * Real.sqrt (w + 1) := by
        have h := Real.log_le_rpow_div (x := w + 1) (ε := (1 / 2 : ℝ))
          (le_of_lt hw1pos) (by norm_num)
        have hrew : (w + 1) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * Real.sqrt (w + 1) := by
          rw [Real.sqrt_eq_rpow]; ring
        linarith [h, hrew]
      have hsqrt : (6000 : ℝ) ≤ Real.sqrt (w + 1) := by
        rw [Real.le_sqrt (by norm_num) (le_of_lt hw1pos)]
        nlinarith [hw]
      rw [le_div_iff₀ hlogw1pos]
      have h1 : 3000 * Real.log (w + 1) ≤ 3000 * (2 * Real.sqrt (w + 1)) :=
        mul_le_mul_of_nonneg_left hlog_le (by norm_num)
      have h2 : (3000 : ℝ) * (2 * Real.sqrt (w + 1)) ≤ w + 1 := by
        nlinarith [hsqrt, Real.sq_sqrt (le_of_lt hw1pos), hw1pos]
      linarith
    linarith

end Work.FIArea3
