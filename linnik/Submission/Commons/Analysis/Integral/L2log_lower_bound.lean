import Mathlib
import Submission.Commons.Analysis.Integral.T_lower_Tlb

namespace Commons.Analysis.Integral

/-- `2*(y-1)/(y+1) ≤ log y` for `y ≥ 1`. -/
lemma two_mul_sub_div_le_log {y : ℝ} (hy : 1 ≤ y) :
    2*(y-1)/(y+1) ≤ Real.log y := by
  rcases eq_or_lt_of_le hy with h | h
  · subst h
    norm_num [Real.log_one]
  · have hz : 0 < y - 1 := by linarith
    have h := log_one_add_ge (y-1) hz
    rw [show (2:ℝ) + (y-1) = y + 1 by ring, show (1:ℝ) + (y-1) = y by ring] at h
    exact h

/-- `2*z/(2+z) ≤ log (1+z)` for `z ≥ 0`. -/
lemma log_one_add_ge_nonneg (z : ℝ) (hz : 0 ≤ z) :
    2*z/(2+z) ≤ Real.log (1+z) := by
  rcases eq_or_lt_of_le hz with h | h
  · rw [← h]; norm_num [Real.log_one]
  · exact log_one_add_ge z h

/-- Rational lower bound for the log-branch term `L2log(s)` when `s ≤ β`:
`L2log(s) ≥ (1-β²/(2(b²+β²)))(log 2 + 2(β-s)/(β+s) + 2w/(2+w))`, `w = s²/(4β²)`, `b = 2-β`. -/
theorem L2log_lower_bound :
  ∀ s β : ℝ, 1/4 ≤ s → 0 < β → s ≤ β →
    Real.log ((4*β^2+s^2)/(2*β*s))*(1 - s^2/(2*((2-β)^2+β^2)))
    ≥ (1 - β^2/(2*((2-β)^2+β^2)))*(Real.log 2 + 2*(β-s)/(β+s)
        + 2*(s^2/(4*β^2))/(2+s^2/(4*β^2))) := by
  intro s β hs hβ hsβ
  have hs_pos : 0 < s := by linarith
  set w : ℝ := s^2/(4*β^2) with hw
  set D : ℝ := 2*((2-β)^2+β^2) with hD
  have hD_pos : 0 < D := by
    rw [hD]
    have h1 := sq_nonneg (2-β)
    have h2 := pow_pos hβ 2
    linarith
  have hw_nonneg : 0 ≤ w := by
    rw [hw]
    have h2 : 0 < 4*β^2 := by positivity
    positivity
  -- (1) B ≥ 0
  have hB_nonneg : 0 ≤ 1 - β^2/D := by
    rw [sub_nonneg, div_le_iff₀ hD_pos]
    rw [hD]
    nlinarith [sq_nonneg (2-β), sq_nonneg β]
  -- (2) A ≥ B
  have hsq_sβ : s^2 ≤ β^2 := by
    have h1 : 0 ≤ β - s := by linarith
    have h2 : 0 ≤ β + s := by linarith
    nlinarith [mul_nonneg h1 h2]
  have hBA : 1 - β^2/D ≤ 1 - s^2/D := by
    have h : s^2/D ≤ β^2/D := div_le_div_of_nonneg_right hsq_sβ hD_pos.le
    linarith
  have hA_nonneg : 0 ≤ 1 - s^2/D := le_trans hB_nonneg hBA
  -- (3) L ≥ M
  have hβs_pos : 0 < β/s := div_pos hβ hs_pos
  have h1w_pos : 0 < 1 + w := by linarith
  have hkey : (4*β^2+s^2)/(2*β*s) = 2*(β/s)*(1+w) := by
    rw [hw]
    field_simp
    ring
  have hL_eq : Real.log ((4*β^2+s^2)/(2*β*s))
      = Real.log 2 + Real.log (β/s) + Real.log (1+w) := by
    have h41 : Real.log (2 * (β/s)) = Real.log 2 + Real.log (β/s) :=
      Real.log_mul (by norm_num) (ne_of_gt hβs_pos)
    have h42 : Real.log (2 * (β/s) * (1+w)) = Real.log (2*(β/s)) + Real.log (1+w) :=
      Real.log_mul (by positivity) (ne_of_gt h1w_pos)
    rw [hkey, h42, h41]
  have hlogβs : 2*(β-s)/(β+s) ≤ Real.log (β/s) := by
    have hge : 1 ≤ β/s := by rw [le_div_iff₀ hs_pos]; linarith
    have h := two_mul_sub_div_le_log hge
    have hval : 2*((β/s) - 1)/((β/s) + 1) = 2*(β-s)/(β+s) := by
      field_simp
    rwa [hval] at h
  have hlog1w : 2*w/(2+w) ≤ Real.log (1+w) := log_one_add_ge_nonneg w hw_nonneg
  have hLM : Real.log 2 + 2*(β-s)/(β+s) + 2*w/(2+w)
      ≤ Real.log ((4*β^2+s^2)/(2*β*s)) := by
    rw [hL_eq]
    linarith [hlogβs, hlog1w]
  have hM_nonneg : 0 ≤ Real.log 2 + 2*(β-s)/(β+s) + 2*w/(2+w) := by
    have h1 : 0 ≤ 2*(β-s)/(β+s) := by
      have hh : 0 ≤ (β-s)/(β+s) := div_nonneg (by linarith) (by linarith)
      have he : 2*(β-s)/(β+s) = 2*((β-s)/(β+s)) := by ring
      rw [he]; exact mul_nonneg (by norm_num) hh
    have h2 : 0 ≤ 2*w/(2+w) := div_nonneg (by linarith) (by linarith)
    have h3 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  -- (4) assemble
  have hfinal : (1 - β^2/D) * (Real.log 2 + 2*(β-s)/(β+s) + 2*w/(2+w))
      ≤ (1 - s^2/D) * Real.log ((4*β^2+s^2)/(2*β*s)) :=
    mul_le_mul hBA hLM hM_nonneg hA_nonneg
  calc Real.log ((4*β^2+s^2)/(2*β*s)) * (1 - s^2/D)
      = (1 - s^2/D) * Real.log ((4*β^2+s^2)/(2*β*s)) := by ring
    _ ≥ (1 - β^2/D) * (Real.log 2 + 2*(β-s)/(β+s) + 2*w/(2+w)) := hfinal

end Commons.Analysis.Integral
