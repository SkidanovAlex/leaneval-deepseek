import Mathlib.Data.ENNReal.Inv

namespace Commons.Analysis.ENNReal

lemma natCast_div_natCast_sub_mul_ofReal {d l k : ℕ} (hld : l < d) (hk : 1 ≤ k) :
    (d : ENNReal) / ((k : ENNReal) * ((d : ENNReal) - (l : ENNReal))) =
      ENNReal.ofReal ((d : ℝ) / ((k : ℝ) * ((d : ℝ) - (l : ℝ)))) := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hkR
  have hdR : (l : ℝ) < (d : ℝ) := by exact_mod_cast hld
  have hsub0 : (0 : ℝ) < (d : ℝ) - (l : ℝ) := sub_pos.mpr hdR
  have hden0 : (0 : ℝ) < (k : ℝ) * ((d : ℝ) - (l : ℝ)) := mul_pos hk0 hsub0
  rw [ENNReal.ofReal_div_of_pos hden0]
  rw [ENNReal.ofReal_mul hk0.le]
  rw [ENNReal.ofReal_sub (d : ℝ) (by positivity : (0 : ℝ) ≤ (l : ℝ))]
  simp

end Commons.Analysis.ENNReal