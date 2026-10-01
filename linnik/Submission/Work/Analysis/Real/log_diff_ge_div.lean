import Mathlib

namespace Work.Analysis.Real

/-- For naturals `1 ≤ m ≤ n ≤ N`, the gap `n - m` is at most
`N * (log n - log m)`. -/
private lemma sub_le_N_mul_log_sub (N m n : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) (hnN : n ≤ N) :
    (n : ℝ) - (m : ℝ) ≤ (N : ℝ) * (Real.log (n : ℝ) - Real.log (m : ℝ)) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hn1 : 1 ≤ n := le_trans hm1 hmn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hnNR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have hX : 0 ≤ Real.log (n : ℝ) - Real.log (m : ℝ) := by
    have := Real.log_le_log hmpos hmnR
    linarith
  have hlog : Real.log ((m : ℝ) / (n : ℝ)) ≤ (m : ℝ) / (n : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (ne_of_gt hmpos) (ne_of_gt hnpos)] at hlog
  have h1 : (n : ℝ) * (1 - (m : ℝ) / (n : ℝ)) ≤
      (n : ℝ) * (Real.log (n : ℝ) - Real.log (m : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hnpos)
  have h2 : (n : ℝ) * (1 - (m : ℝ) / (n : ℝ)) = (n : ℝ) - (m : ℝ) := by
    field_simp
  rw [h2] at h1
  have h3 : (n : ℝ) * (Real.log (n : ℝ) - Real.log (m : ℝ)) ≤
      (N : ℝ) * (Real.log (n : ℝ) - Real.log (m : ℝ)) :=
    mul_le_mul_of_nonneg_right hnNR hX
  linarith

lemma log_diff_ge_div (m n N : ℕ) (hm : m ∈ Finset.Icc 1 N) (hn : n ∈ Finset.Icc 1 N) :
    |(m : ℝ) - (n : ℝ)| ≤ (N : ℝ) * |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  rcases le_total m n with hmn | hnm
  · have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hlogmle : Real.log (m : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log hmpos hmnR
    have key := sub_le_N_mul_log_sub N m n hm1 hmn hnN
    rw [abs_of_nonpos (by linarith : (m : ℝ) - (n : ℝ) ≤ 0),
        abs_of_nonpos (by linarith : Real.log (m : ℝ) - Real.log (n : ℝ) ≤ 0)]
    linarith
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    have hlognle : Real.log (n : ℝ) ≤ Real.log (m : ℝ) := Real.log_le_log hnpos hnmR
    have key := sub_le_N_mul_log_sub N n m hn1 hnm hmN
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ)),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.log (m : ℝ) - Real.log (n : ℝ))]
    linarith

end Work.Analysis.Real
