import Mathlib
import Submission.Work.TMC16Core.Defs

set_option linter.unusedVariables false

namespace Work.TMC16Core.Assembly

/-- Elementary numerical bound: for `Q ≥ 20`, `Q ^ (8/9) ≤ (3/4) * Q`.
This is the arithmetic content of `hyDeltaBin`: the exponent `8/9 < 1` makes the
power of `Q` negligible against `Q` itself, and `20 ≥ (4/3)^9` makes the
constant `3/4` sufficient. -/
lemma rpow_eightninths_le_threequarters (Q : ℝ) (hQ : 20 ≤ Q) :
    Q ^ (8 / 9 : ℝ) ≤ (3 / 4) * Q := by
  have hQpos : (0 : ℝ) < Q := lt_of_lt_of_le (by norm_num) hQ
  have hQle : (0 : ℝ) ≤ Q := le_of_lt hQpos
  -- `Q^(1/9) ≥ 4/3`, because `(4/3)^9 ≤ 20 ≤ Q`.
  have hkey : (4 / 3 : ℝ) ≤ Q ^ ((9 : ℝ)⁻¹) := by
    rw [Real.le_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 4 / 3) hQle
      (by norm_num : (0 : ℝ) < 9)]
    have h2 : ((4 / 3 : ℝ)) ^ (9 : ℝ) = ((4 / 3 : ℝ)) ^ 9 := by norm_num
    rw [h2]
    have h3 : ((4 / 3 : ℝ)) ^ 9 ≤ (20 : ℝ) := by norm_num
    linarith
  set t : ℝ := Q ^ ((9 : ℝ)⁻¹) with ht
  have hQ9 : t ^ 9 = Q := by
    rw [ht]
    exact Real.rpow_inv_natCast_pow hQle (by norm_num : (9 : ℕ) ≠ 0)
  have hQ89 : Q ^ (8 / 9 : ℝ) = t ^ 8 := by
    rw [ht]
    have h1 : (Q ^ ((9 : ℝ)⁻¹)) ^ (8 : ℝ) = Q ^ (8 / 9 : ℝ) := by
      rw [← Real.rpow_mul hQle ((9 : ℝ)⁻¹) 8]
      rw [show ((9 : ℝ)⁻¹) * 8 = (8 / 9 : ℝ) by norm_num]
    rw [← h1]
    norm_num
  rw [hQ89, ← hQ9]
  have h1 : (1 : ℝ) ≤ (3 / 4) * t := by
    have := mul_le_mul_of_nonneg_left hkey (by norm_num : (0 : ℝ) ≤ 3 / 4)
    linarith
  calc t ^ 8 = t ^ 8 * 1 := by ring
    _ ≤ t ^ 8 * ((3 / 4) * t) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (3 / 4) * t ^ 9 := by ring

theorem hyDeltaBin {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ} {y : ℤ}
    (hΔpos : ∀ i, 0 < Δ i) (hΔup : Δ n < 1 / ((q (n + 1) : ℝ)))
    (hqn : (0 : ℝ) < (q n : ℝ)) (hqle : (q n : ℝ) ≤ (q (n + 1) : ℝ))
    (hqn1 : 20 ≤ q (n + 1))
    (hybin : (y : ℝ) ≤ max (Real.rpow (q (n + 1) : ℝ) (8 / 9)) ((q n : ℝ) / 20)) :
    (y : ℝ) * Δ n ≤ 3 / 4 := by
  set Q : ℝ := (q (n + 1) : ℝ) with hQdef
  set P : ℝ := (q n : ℝ) with hPdef
  have hQ20 : (20 : ℝ) ≤ Q := by rw [hQdef]; exact_mod_cast hqn1
  have hQpos : (0 : ℝ) < Q := lt_of_lt_of_le (by norm_num) hQ20
  have hPle : P ≤ Q := by rw [hPdef, hQdef]; exact hqle
  have hnum : Q ^ (8 / 9 : ℝ) ≤ (3 / 4) * Q := rpow_eightninths_le_threequarters Q hQ20
  by_cases hy : (y : ℝ) ≤ 0
  · have : (y : ℝ) * Δ n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hy (le_of_lt (hΔpos n))
    linarith
  · have hypos : 0 < (y : ℝ) := not_le.mp hy
    have hlt : (y : ℝ) * Δ n < (y : ℝ) * (1 / Q) := mul_lt_mul_of_pos_left hΔup hypos
    have hbound : (y : ℝ) / Q ≤ 3 / 4 := by
      rcases le_max_iff.mp hybin with h | h
      · -- `y ≤ Q^(8/9)`: `y/Q ≤ Q^(8/9)/Q ≤ 3/4`
        have h1 : (y : ℝ) / Q ≤ Q ^ (8 / 9 : ℝ) / Q :=
          div_le_div_of_nonneg_right h hQpos.le
        have h2 : Q ^ (8 / 9 : ℝ) / Q ≤ 3 / 4 := by
          rw [div_le_iff₀ hQpos]; exact hnum
        linarith
      · -- `y ≤ P/20`: `y/Q ≤ (P/20)/Q ≤ 1/20 ≤ 3/4`
        have h1 : (y : ℝ) / Q ≤ (P / 20) / Q := div_le_div_of_nonneg_right h hQpos.le
        have h2 : (P / 20) / Q ≤ 1 / 20 := by
          rw [div_le_iff₀ hQpos, show (1 / 20 : ℝ) * Q = Q / 20 by ring]
          exact div_le_div_of_nonneg_right hPle (by norm_num)
        linarith
    calc (y : ℝ) * Δ n ≤ (y : ℝ) * (1 / Q) := le_of_lt hlt
      _ = (y : ℝ) / Q := by rw [mul_one_div]
      _ ≤ 3 / 4 := hbound

end Work.TMC16Core.Assembly
