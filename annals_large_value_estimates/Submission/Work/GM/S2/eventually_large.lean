import Mathlib
import Submission.Work.GM.S2.pair_sum_defs

namespace Work.GM.S2

/-- For `N` large enough the quantity `M N = N^{6/5}` is dominated by powers of `N`
with the exponents required by the `S₂` estimates. -/
theorem eventually_large (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) (hηδ : 24 * η ≤ δ) (hη1 : 6 * η ≤ 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (3 * (Submission.LargeValues.M N) ^ η ≤ (N : ℝ)) ∧
      ((Submission.LargeValues.M N) ^ η ≤ (N : ℝ) ^ (δ / 4)) ∧
      ((Submission.LargeValues.M N) ^ (2 * η) ≤ (N : ℝ) ^ (δ / 4)) := by
  refine ⟨9, fun N hN => ?_⟩
  have hN9 : (9 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hXpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hX1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hpow_η : (Submission.LargeValues.M N) ^ η = (N : ℝ) ^ ((6 / 5 : ℝ) * η) := by
    rw [Submission.LargeValues.M]
    exact (Real.rpow_mul (le_of_lt hXpos) (6 / 5 : ℝ) η).symm
  have hpow_2η : (Submission.LargeValues.M N) ^ (2 * η)
      = (N : ℝ) ^ ((6 / 5 : ℝ) * (2 * η)) := by
    rw [Submission.LargeValues.M]
    exact (Real.rpow_mul (le_of_lt hXpos) (6 / 5 : ℝ) (2 * η)).symm
  -- the numeric input: `3 ≤ N^(4/5)` for `N ≥ 9`
  have h3 : (3 : ℝ) ≤ (N : ℝ) ^ ((4 / 5 : ℝ)) := by
    have h1 : (3 : ℝ) ≤ Real.sqrt (N : ℝ) := by
      have h : Real.sqrt 9 ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt hN9
      rwa [show Real.sqrt 9 = (3 : ℝ) by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
    rw [Real.sqrt_eq_rpow] at h1
    have h3' : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (4 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hpow_η]
    have hstep : (N : ℝ) ^ ((6 / 5 : ℝ) * η) ≤ (N : ℝ) ^ ((1 / 5 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    calc 3 * (N : ℝ) ^ ((6 / 5 : ℝ) * η)
        ≤ 3 * (N : ℝ) ^ ((1 / 5 : ℝ)) := by linarith
      _ ≤ (N : ℝ) ^ ((4 / 5 : ℝ)) * (N : ℝ) ^ ((1 / 5 : ℝ)) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (N : ℝ) ^ ((4 / 5 : ℝ) + (1 / 5 : ℝ)) :=
          (Real.rpow_add hXpos (4 / 5 : ℝ) (1 / 5 : ℝ)).symm
      _ = (N : ℝ) := by rw [show (4 / 5 : ℝ) + 1 / 5 = 1 by norm_num, Real.rpow_one]
  · rw [hpow_η]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    linarith
  · rw [hpow_2η]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    linarith

end Work.GM.S2
