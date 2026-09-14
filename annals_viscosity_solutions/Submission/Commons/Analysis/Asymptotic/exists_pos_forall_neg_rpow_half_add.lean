import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Asymptotic

theorem exists_pos_forall_neg_rpow_half_add {A B C : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ∃ ρ₀ > 0, ∀ ρ ∈ Set.Ioo (0:ℝ) ρ₀, -A * ρ ^ ((1:ℝ)/2) + B * ρ + C * ρ ^ 2 < 0 := by
  set s : ℝ := A / (B + C + 1) with hs
  have hden_pos : 0 < B + C + 1 := by linarith
  have hs_pos : 0 < s := by rw [hs]; exact div_pos hA hden_pos
  have hs_mul : (B + C) * s < A := by
    rw [hs, ← mul_div_assoc, div_lt_iff₀ hden_pos]
    nlinarith
  refine ⟨min 1 (s ^ 2), lt_min one_pos (pow_pos hs_pos 2), ?_⟩
  intro ρ hρ
  rw [Set.mem_Ioo] at hρ
  obtain ⟨hρpos, hρlt⟩ := hρ
  set t : ℝ := Real.sqrt ρ with ht
  have ht_pos : 0 < t := by rw [ht]; exact Real.sqrt_pos.mpr hρpos
  have hρlt_s2 : ρ < s ^ 2 := lt_of_lt_of_le hρlt (min_le_right _ _)
  have ht_lt_s : t < s := by
    rw [ht]
    have h := Real.sqrt_lt_sqrt hρpos.le hρlt_s2
    rwa [Real.sqrt_sq hs_pos.le] at h
  have hρlt_one : ρ < 1 := lt_of_lt_of_le hρlt (min_le_left _ _)
  have ht_lt_one : t < 1 := by
    rw [ht]
    have h := Real.sqrt_lt_sqrt hρpos.le hρlt_one
    rwa [Real.sqrt_one] at h
  have ht_cube_le : t ^ 3 ≤ t := by
    have ht2_le : t ^ 2 ≤ 1 := by
      have h := pow_le_pow_left₀ ht_pos.le ht_lt_one.le 2
      simpa using h
    calc t ^ 3 = t ^ 2 * t := by ring
      _ ≤ 1 * t := mul_le_mul_of_nonneg_right ht2_le ht_pos.le
      _ = t := one_mul t
  have ht_cube_lt_s : t ^ 3 < s := lt_of_le_of_lt ht_cube_le ht_lt_s
  have hBtC : B * t + C * t ^ 3 ≤ (B + C) * s := by
    have h1 : B * t ≤ B * s := mul_le_mul_of_nonneg_left (le_of_lt ht_lt_s) hB
    have h2 : C * t ^ 3 ≤ C * s := mul_le_mul_of_nonneg_left (le_of_lt ht_cube_lt_s) hC
    nlinarith
  have hkey : -A + B * t + C * t ^ 3 < 0 := by
    have : B * t + C * t ^ 3 < A := lt_of_le_of_lt hBtC hs_mul
    linarith
  have hrpow : ρ ^ ((1:ℝ)/2) = t := by
    rw [ht]
    exact (Real.sqrt_eq_rpow ρ).symm
  have hsq : ρ = t ^ 2 := by
    rw [ht]
    exact (Real.sq_sqrt hρpos.le).symm
  have hexpr : -A * ρ ^ ((1:ℝ)/2) + B * ρ + C * ρ ^ 2 = t * (-A + B * t + C * t ^ 3) := by
    rw [hrpow, hsq]
    ring
  rw [hexpr]
  exact mul_neg_of_pos_of_neg ht_pos hkey

end Commons.Analysis.Asymptotic