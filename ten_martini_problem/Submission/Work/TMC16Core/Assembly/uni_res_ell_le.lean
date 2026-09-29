import Mathlib

namespace Work.TMC16Core.Assembly

/-- Auxiliary arithmetic bound: if `10 ^ 9 ≤ P` then `10 * P ^ (8/9) ≤ P`.
Indeed `P ^ (1/9) ≥ 10`, so `10 * P ^ (8/9) ≤ P ^ (1/9) * P ^ (8/9) = P`. -/
lemma ten_mul_rpow_eight_ninths_le_self (P : ℕ) (hP : 10 ^ 9 ≤ P) :
    10 * (P : ℝ) ^ ((8 : ℝ) / 9) ≤ (P : ℝ) := by
  have hPpos : (0 : ℝ) < (P : ℝ) := by
    have : 0 < P := lt_of_lt_of_le (by norm_num) hP
    exact_mod_cast this
  have hP' : (10 : ℝ) ^ 9 ≤ (P : ℝ) := by
    have : (10 : ℝ) ^ 9 = ((10 ^ 9 : ℕ) : ℝ) := by norm_num
    rw [this]; exact_mod_cast hP
  have hxz : (10 : ℝ) ≤ (P : ℝ) ^ ((9 : ℝ)⁻¹) := by
    rw [Real.le_rpow_inv_iff_of_pos (by norm_num) (le_of_lt hPpos) (by norm_num)]
    simpa using hP'
  have h59 : (P : ℝ) ^ ((9 : ℝ)⁻¹) * (P : ℝ) ^ ((8 : ℝ) / 9) = (P : ℝ) := by
    rw [← Real.rpow_add hPpos ((9 : ℝ)⁻¹) ((8 : ℝ) / 9)]
    have : (9 : ℝ)⁻¹ + (8 : ℝ) / 9 = 1 := by norm_num
    rw [this, Real.rpow_one]
  calc 10 * (P : ℝ) ^ ((8 : ℝ) / 9)
      ≤ (P : ℝ) ^ ((9 : ℝ)⁻¹) * (P : ℝ) ^ ((8 : ℝ) / 9) :=
        mul_le_mul_of_nonneg_right hxz (Real.rpow_nonneg (le_of_lt hPpos) _)
    _ = (P : ℝ) := h59

theorem uni_res_ell_le {P qn ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hP : 10 ^ 9 ≤ P) (hqn : 0 < qn)
    (h : (ℓ : ℝ) ≤ Real.rpow (P : ℝ) (8 / 9) / (qn : ℝ)) :
    10 * (ℓ : ℤ) * (qn : ℤ) ≤ (P : ℤ) := by
  have _ := hℓ
  have hqn' : (0 : ℝ) < (qn : ℝ) := by exact_mod_cast hqn
  have h1 : (ℓ : ℝ) * (qn : ℝ) ≤ (P : ℝ) ^ ((8 : ℝ) / 9) := (le_div_iff₀ hqn').mp h
  have h2 : 10 * (ℓ : ℝ) * (qn : ℝ) ≤ (P : ℝ) := by
    calc 10 * (ℓ : ℝ) * (qn : ℝ) = 10 * ((ℓ : ℝ) * (qn : ℝ)) := by ring
      _ ≤ 10 * (P : ℝ) ^ ((8 : ℝ) / 9) := by
            apply mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ ≤ (P : ℝ) := ten_mul_rpow_eight_ninths_le_self P hP
  have h3 : (10 * (ℓ : ℤ) * (qn : ℤ) : ℝ) ≤ (P : ℝ) := by
    push_cast
    exact h2
  exact_mod_cast h3

end Work.TMC16Core.Assembly
