import Mathlib

namespace Work.HP.MM2

lemma f_zero_le (J : ℕ) (T : ℝ) (A : ℕ → ℝ) (hT : 1 ≤ T) (hJ : (2:ℝ)^J ≤ T) (hA0 : 0 ≤ A 0) :
    (∑ j ∈ Finset.range (J+1), ((2:ℝ)^(j+1)/T) * ((T/(2:ℝ)^j)^0 * A 0)) ≤ 4 * A 0 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hgeom : (∑ j ∈ Finset.range (J+1), (2:ℝ)^(j+1)) = 2^(J+2) - 2 := by
    have h := geom_sum_mul (2:ℝ) (J+2)
    rw [show (2:ℝ) - 1 = 1 from by norm_num, mul_one] at h
    rw [Finset.sum_range_succ'] at h
    norm_num at h
    linarith
  have hbound : (∑ j ∈ Finset.range (J+1), (2:ℝ)^(j+1)/T) ≤ 4 := by
    rw [← Finset.sum_div, hgeom]
    rw [div_le_iff₀ hTpos]
    have hpow : (2:ℝ)^(J+2) = 4 * (2:ℝ)^J := by rw [pow_add]; ring
    have h4J : 4 * (2:ℝ)^J ≤ 4 * T := by
      have := mul_le_mul_of_nonneg_left hJ (by norm_num : (0:ℝ) ≤ 4)
      linarith
    linarith
  calc (∑ j ∈ Finset.range (J+1), ((2:ℝ)^(j+1)/T) * ((T/(2:ℝ)^j)^0 * A 0))
      = ∑ j ∈ Finset.range (J+1), A 0 * ((2:ℝ)^(j+1)/T) := by
        apply Finset.sum_congr rfl; intro j hj; rw [pow_zero, one_mul]; ring
    _ = A 0 * ∑ j ∈ Finset.range (J+1), (2:ℝ)^(j+1)/T := by rw [Finset.mul_sum]
    _ ≤ A 0 * 4 := by
        apply mul_le_mul_of_nonneg_left hbound hA0
    _ = 4 * A 0 := by ring

end Work.HP.MM2
