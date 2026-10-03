import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.DiscreteCZ

theorem large_const_le (C' A2 Ak p : ℝ) (hp : 2 < p) (hC' : 0 < C') (hA2 : 0 < A2) (hAk : 0 ≤ Ak) :
    C' * (24 * (2 * A2) ^ 2 + 4 * Ak + 100) ^ (2 / (p / (p - 1)) - 1)
        * (2 * A2) ^ (2 - 2 / (p / (p - 1)))
      ≤ 8 * C' * (24 * A2 ^ 2 + 4 * Ak + 100) ^ (2 / (p / (p - 1)) - 1)
        * A2 ^ (2 - 2 / (p / (p - 1))) := by
  set s : ℝ := 2 / (p / (p - 1)) - 1 with hs
  set t : ℝ := 2 - 2 / (p / (p - 1)) with ht
  have hp1 : (0:ℝ) < p - 1 := by linarith
  have hPpos : (0:ℝ) < p / (p - 1) := by positivity
  have hP1 : (1:ℝ) < p / (p - 1) := by
    rw [one_lt_div hp1]; linarith
  have hP2 : p / (p - 1) ≤ 2 := by
    rw [div_le_iff₀ hp1]; linarith
  have hs0 : 0 ≤ s := by
    rw [hs]
    have h : 1 ≤ 2 / (p / (p - 1)) := by
      rw [le_div_iff₀ hPpos]; simpa using hP2
    linarith
  have hs1 : s ≤ 1 := by
    rw [hs]
    have h : 2 / (p / (p - 1)) ≤ 2 := by
      rw [div_le_iff₀ hPpos]; linarith
    linarith
  have ht1 : t ≤ 1 := by
    rw [ht]
    have h : 1 ≤ 2 / (p / (p - 1)) := by
      rw [le_div_iff₀ hPpos]; simpa using hP2
    linarith
  set U : ℝ := 24 * (2 * A2) ^ 2 + 4 * Ak + 100 with hU
  set V : ℝ := 24 * A2 ^ 2 + 4 * Ak + 100 with hV
  have hUpos : 0 < U := by rw [hU]; nlinarith [hAk, sq_nonneg (2 * A2)]
  have hVpos : 0 < V := by rw [hV]; nlinarith [hAk, sq_nonneg A2]
  have hUV : U ≤ 4 * V := by rw [hU, hV]; nlinarith [hAk]
  have h2t : (2:ℝ) ^ t ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) ht1
    simpa [Real.rpow_one] using h
  have hU4V : U ^ s ≤ 4 * V ^ s := by
    have h1 : U ^ s ≤ (4 * V) ^ s := Real.rpow_le_rpow (le_of_lt hUpos) hUV hs0
    have h2 : (4 * V) ^ s = (4:ℝ) ^ s * V ^ s := Real.mul_rpow (by norm_num) (le_of_lt hVpos)
    have h3 : (4:ℝ) ^ s ≤ 4 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) hs1
      simpa [Real.rpow_one] using h
    calc U ^ s ≤ (4 * V) ^ s := h1
      _ = (4:ℝ) ^ s * V ^ s := h2
      _ ≤ 4 * V ^ s := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (le_of_lt hVpos) s)
  have hmain : U ^ s * (2:ℝ) ^ t ≤ 8 * V ^ s := by
    have h1 : U ^ s * (2:ℝ) ^ t ≤ U ^ s * 2 :=
      mul_le_mul_of_nonneg_left h2t (Real.rpow_nonneg (le_of_lt hUpos) s)
    have h2 : U ^ s * 2 ≤ 8 * V ^ s := by nlinarith [hU4V]
    linarith
  have hA2tpos : 0 < A2 ^ t := Real.rpow_pos_of_pos hA2 t
  have h2A2t : (2 * A2) ^ t = (2:ℝ) ^ t * A2 ^ t := Real.mul_rpow (by norm_num) (le_of_lt hA2)
  calc C' * U ^ s * (2 * A2) ^ t
      = C' * (U ^ s * (2:ℝ) ^ t) * A2 ^ t := by rw [h2A2t]; ring
    _ ≤ C' * (8 * V ^ s) * A2 ^ t := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hA2tpos)
        exact mul_le_mul_of_nonneg_left hmain (le_of_lt hC')
    _ = 8 * C' * V ^ s * A2 ^ t := by ring

end Commons.Analysis.DiscreteCZ