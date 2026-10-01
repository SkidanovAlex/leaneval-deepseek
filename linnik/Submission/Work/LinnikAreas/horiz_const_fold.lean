import Mathlib

namespace Work.LinnikAreas

theorem horiz_const_fold (CZ CL : ℝ) (hCZ : 0 < CZ) (hCL : 0 < CL) :
    ∃ KH : ℝ, 0 < KH ∧ ∀ {N : ℕ} [NeZero N] {T D1 D2 : ℝ}, 1 ≤ T → 0 ≤ D1 → 0 ≤ D2 →
      (2 / Real.pi) * CZ * (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * D1
          + (Real.log (2 * N) + Real.log (2 + T) + 6) * D2)
        ≤ KH * ((N : ℝ) ^ ((1 : ℝ) / 4) * D1
          + (Real.log (2 * N) + Real.log (2 + T)) * D2) := by
  -- The constant `6` inside the logarithmic factor is absorbed by the
  -- `+ 7` in `CL + 7`, using `Real.log (2*N) + Real.log (2+T) ≥ Real.log 6 > 1`.
  refine ⟨(2 / Real.pi) * CZ * (CL + 7), ?_, ?_⟩
  · positivity
  · intro N _ T D1 D2 hT hD1 hD2
    have hNpos : 0 < (N : ℝ) := by
      have : (0 : ℕ) < N := Nat.pos_of_ne_zero (NeZero.ne N)
      exact_mod_cast this
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
      have : (1 : ℕ) ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
      exact_mod_cast this
    have hA : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * D1 :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt hNpos) _) hD1
    have hlog6gt1 : (1 : ℝ) < Real.log 6 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 6)]
      linarith [Real.exp_one_lt_three]
    have hB : Real.log 6 ≤ Real.log (2 * (N : ℝ)) + Real.log (2 + T) := by
      have hlog1 : Real.log 2 ≤ Real.log (2 * (N : ℝ)) := by
        apply Real.log_le_log (by norm_num); linarith
      have hlog2 : Real.log 3 ≤ Real.log (2 + T) := by
        apply Real.log_le_log (by norm_num); linarith
      have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith
    have hB1 : 1 < Real.log (2 * (N : ℝ)) + Real.log (2 + T) := by linarith
    have hBpos : 0 < Real.log (2 * (N : ℝ)) + Real.log (2 + T) := by linarith
    have key : CL * ((N : ℝ) ^ ((1 : ℝ) / 4) * D1)
          + (Real.log (2 * (N : ℝ)) + Real.log (2 + T) + 6) * D2
        ≤ (CL + 7) * (((N : ℝ) ^ ((1 : ℝ) / 4) * D1)
          + (Real.log (2 * (N : ℝ)) + Real.log (2 + T)) * D2) := by
      have h1 : CL * ((N : ℝ) ^ ((1 : ℝ) / 4) * D1)
          ≤ (CL + 7) * ((N : ℝ) ^ ((1 : ℝ) / 4) * D1) :=
        mul_le_mul_of_nonneg_right (by linarith) hA
      have h2 : (Real.log (2 * (N : ℝ)) + Real.log (2 + T) + 6) * D2
          ≤ (CL + 7) * (Real.log (2 * (N : ℝ)) + Real.log (2 + T)) * D2 := by
        apply mul_le_mul_of_nonneg_right _ hD2
        nlinarith [hB1, hCL, mul_nonneg (le_of_lt hCL) (le_of_lt hBpos)]
      nlinarith [h1, h2]
    have hc : 0 ≤ (2 / Real.pi) * CZ := by positivity
    have hmain : (2 / Real.pi) * CZ * (CL * ((N : ℝ) ^ ((1 : ℝ) / 4) * D1)
          + (Real.log (2 * (N : ℝ)) + Real.log (2 + T) + 6) * D2)
        ≤ (2 / Real.pi) * CZ * ((CL + 7) * (((N : ℝ) ^ ((1 : ℝ) / 4) * D1)
          + (Real.log (2 * (N : ℝ)) + Real.log (2 + T)) * D2)) :=
      mul_le_mul_of_nonneg_left key hc
    have hLHS : (2 / Real.pi) * CZ * (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * D1
          + (Real.log (2 * N) + Real.log (2 + T) + 6) * D2)
        = (2 / Real.pi) * CZ * (CL * ((N : ℝ) ^ ((1 : ℝ) / 4) * D1)
          + (Real.log (2 * (N : ℝ)) + Real.log (2 + T) + 6) * D2) := by ring
    have hRHS : ((2 / Real.pi) * CZ * (CL + 7)) * ((N : ℝ) ^ ((1 : ℝ) / 4) * D1
          + (Real.log (2 * N) + Real.log (2 + T)) * D2)
        = (2 / Real.pi) * CZ * ((CL + 7) * (((N : ℝ) ^ ((1 : ℝ) / 4) * D1)
          + (Real.log (2 * (N : ℝ)) + Real.log (2 + T)) * D2)) := by ring
    rw [hLHS, hRHS]
    exact hmain

end Work.LinnikAreas
