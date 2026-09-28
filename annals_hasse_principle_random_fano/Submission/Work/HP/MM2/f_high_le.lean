import Mathlib

namespace Work.HP.MM2

lemma f_high_le (J m : ℕ) (T : ℝ) (A : ℕ → ℝ) (hT : 1 ≤ T) (hm : 2 ≤ m) (hAm : 0 ≤ A m) :
    (∑ j ∈ Finset.range (J+1), ((2:ℝ)^(j+1)/T) * ((T/(2:ℝ)^j)^m * A m)) ≤ 4 * T^(m-1) * A m := by
  have hT0 : T ≠ 0 := by linarith
  have hm1 : 1 ≤ m := by omega
  have hnonneg : 0 ≤ T^(m-1) * A m := mul_nonneg (pow_nonneg (by linarith) _) hAm
  -- Each summand factors as `(2^(j+1) / 2^(j*m)) * (T^(m-1) * A m)`.
  have hterm : ∀ j, ((2:ℝ)^(j+1)/T) * ((T/(2:ℝ)^j)^m * A m)
      = ((2:ℝ)^(j+1)/(2:ℝ)^(j*m)) * (T^(m-1) * A m) := by
    intro j
    rw [div_pow, pow_mul]
    rw [pow_sub₀ T hT0 hm1]
    have h2 : (2:ℝ)^(j*m) ≠ 0 := by positivity
    field_simp
  -- The geometric factor is bounded by `2 / 2^j`.
  have hbound : ∀ j, (2:ℝ)^(j+1)/(2:ℝ)^(j*m) ≤ 2/(2:ℝ)^j := by
    intro j
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2^(j*m)) (by positivity : (0:ℝ) < 2^j)]
    have h1 : (2:ℝ)^(j+1) * 2^j = 2^(2*j+1) := by rw [← pow_add]; congr 1; omega
    have h2 : (2:ℝ) * 2^(j*m) = 2^(j*m+1) := (pow_succ' (2:ℝ) (j*m)).symm
    rw [h1, h2]
    apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
    have h : j*2 ≤ j*m := Nat.mul_le_mul_left j hm
    omega
  -- The geometric sum is at most `4`.
  have hgeom : (∑ j ∈ Finset.range (J+1), 2/(2:ℝ)^j) ≤ 4 := by
    have h : (∑ j ∈ Finset.range (J+1), 2/(2:ℝ)^j)
        = 2 * (∑ j ∈ Finset.range (J+1), (1/2:ℝ)^j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [div_pow]
      rw [show (1:ℝ)^j = 1 by simp]
      ring
    rw [h]
    have h2 := sum_geometric_two_le (J+1)
    linarith
  calc
    (∑ j ∈ Finset.range (J+1), ((2:ℝ)^(j+1)/T) * ((T/(2:ℝ)^j)^m * A m))
        = ∑ j ∈ Finset.range (J+1), ((2:ℝ)^(j+1)/(2:ℝ)^(j*m)) * (T^(m-1) * A m) := by
          apply Finset.sum_congr rfl; intro j hj; exact hterm j
    _ = (∑ j ∈ Finset.range (J+1), (2:ℝ)^(j+1)/(2:ℝ)^(j*m)) * (T^(m-1) * A m) :=
          (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ j ∈ Finset.range (J+1), 2/(2:ℝ)^j) * (T^(m-1) * A m) :=
          mul_le_mul_of_nonneg_right (Finset.sum_le_sum (fun j hj => hbound j)) hnonneg
    _ ≤ 4 * (T^(m-1) * A m) := mul_le_mul_of_nonneg_right hgeom hnonneg
    _ = 4 * T^(m-1) * A m := by ring

end Work.HP.MM2
