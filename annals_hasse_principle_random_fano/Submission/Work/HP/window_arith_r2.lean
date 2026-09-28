import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP

/-- `2 ^ (m * logb 2 z) = z ^ m` for `z > 0`. -/
lemma two_rpow_mul_logb (z : ℝ) (hz : 0 < z) (m : ℝ) :
    (2 : ℝ) ^ (m * Real.logb 2 z) = z ^ m := by
  rw [mul_comm m (Real.logb 2 z)]
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (Real.logb 2 z) m]
  rw [Real.rpow_logb (by norm_num) (by norm_num) hz]

theorem window_arith_r2 (n : ℕ) (hn : 2 ≤ n)
    (Kmink : ℝ) (hKmink : 1 ≤ Kmink)
    (Cdya : ℝ) (hCdya : 0 < Cdya)
    (hdya : ∀ (X Y L' : ℝ), 1 ≤ X → 1 ≤ Y → 0 ≤ L' →
      (∑ k ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range (⌈L'⌉₊ + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ ⌈L'⌉₊ ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
          X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
            + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
            + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)
        else 0))
      ≤ Cdya * X ^ 2 * Y ^ 2 * 2 ^ (((n + 1) - 2) * L')) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X Y Δ : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ Δ →
      (∑ k ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range (⌈Real.logb 2 ((2 : ℝ) ^ 2 * Kmink * (Δ + 1))⌉₊ + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ ⌈Real.logb 2 ((2 : ℝ) ^ 2 * Kmink * (Δ + 1))⌉₊
            ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
          X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
            + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
            + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)
        else 0))
      ≤ K * X ^ 2 * Y ^ 2 * Δ ^ (n - 1) := by
  refine ⟨Cdya * ((2 : ℝ) ^ 2 * Kmink) ^ (n - 1) * (2 : ℝ) ^ (n - 1), ?_, ?_⟩
  · have hC : (0 : ℝ) < (2 : ℝ) ^ 2 * Kmink := by nlinarith [hKmink]
    exact mul_pos (mul_pos hCdya (pow_pos hC (n - 1))) (pow_pos (by norm_num) (n - 1))
  · intro X Y Δ hX hY hΔ
    set z : ℝ := (2 : ℝ) ^ 2 * Kmink * (Δ + 1) with hzdef
    have hCpos : (0 : ℝ) < (2 : ℝ) ^ 2 * Kmink := by nlinarith [hKmink]
    have hzpos : 0 < z := by
      rw [hzdef]; exact mul_pos hCpos (by linarith)
    have hzone : 1 ≤ z := by
      rw [hzdef]
      have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ 2 * Kmink := by nlinarith [hKmink]
      have h2 : (2 : ℝ) ≤ Δ + 1 := by linarith
      have hb : (0 : ℝ) ≤ (2 : ℝ) ^ 2 * Kmink := le_of_lt hCpos
      have := mul_le_mul h4 h2 (by norm_num) hb
      linarith [this]
    have hL : 0 ≤ Real.logb 2 z := Real.logb_nonneg (by norm_num) hzone
    have hsum := hdya X Y (Real.logb 2 z) hX hY hL
    refine le_trans hsum ?_
    have hcast : ((n : ℝ) + 1 - 2) = ((n - 1 : ℕ) : ℝ) := by
      have h1 : (1 : ℕ) ≤ n := by omega
      have h2 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub h1, Nat.cast_one]
      rw [h2]; ring
    have hrpow : (2 : ℝ) ^ (((n : ℝ) + 1 - 2) * Real.logb 2 z) = z ^ (n - 1) := by
      rw [hcast, two_rpow_mul_logb z hzpos ((n - 1 : ℕ) : ℝ), Real.rpow_natCast]
    rw [hrpow]
    have hz_le : z ≤ ((2 : ℝ) ^ 2 * Kmink) * (2 * Δ) := by
      rw [hzdef]
      have hC : (0 : ℝ) ≤ (2 : ℝ) ^ 2 * Kmink := le_of_lt hCpos
      have hle : Δ + 1 ≤ 2 * Δ := by linarith
      exact mul_le_mul_of_nonneg_left hle hC
    have hpow_le : z ^ (n - 1) ≤ (((2 : ℝ) ^ 2 * Kmink) * (2 * Δ)) ^ (n - 1) :=
      pow_le_pow_left₀ (le_of_lt hzpos) hz_le (n - 1)
    have hmul1 : (((2 : ℝ) ^ 2 * Kmink) * (2 * Δ)) ^ (n - 1)
        = ((2 : ℝ) ^ 2 * Kmink) ^ (n - 1) * (2 * Δ) ^ (n - 1) := mul_pow _ _ _
    have hmul2 : (2 * Δ) ^ (n - 1) = 2 ^ (n - 1) * Δ ^ (n - 1) := mul_pow _ _ _
    have hfinal : z ^ (n - 1) ≤ ((2 : ℝ) ^ 2 * Kmink) ^ (n - 1) * 2 ^ (n - 1) * Δ ^ (n - 1) := by
      calc z ^ (n - 1) ≤ (((2 : ℝ) ^ 2 * Kmink) * (2 * Δ)) ^ (n - 1) := hpow_le
        _ = ((2 : ℝ) ^ 2 * Kmink) ^ (n - 1) * 2 ^ (n - 1) * Δ ^ (n - 1) := by
              rw [hmul1, hmul2]; ring
    have hXY : (0 : ℝ) < Cdya * X ^ 2 * Y ^ 2 := by
      have hXp : (0 : ℝ) < X := by linarith
      have hYp : (0 : ℝ) < Y := by linarith
      positivity
    calc Cdya * X ^ 2 * Y ^ 2 * z ^ (n - 1)
        ≤ Cdya * X ^ 2 * Y ^ 2 * (((2 : ℝ) ^ 2 * Kmink) ^ (n - 1) * 2 ^ (n - 1) * Δ ^ (n - 1)) :=
          mul_le_mul_of_nonneg_left hfinal (le_of_lt hXY)
      _ = Cdya * ((2 : ℝ) ^ 2 * Kmink) ^ (n - 1) * (2 : ℝ) ^ (n - 1) * X ^ 2 * Y ^ 2 * Δ ^ (n - 1) := by ring

end Work.HP
