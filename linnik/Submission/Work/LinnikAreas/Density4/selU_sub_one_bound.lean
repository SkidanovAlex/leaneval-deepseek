import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.LinnikAreas.Density4.selberg_U_decay
import Submission.Work.LinnikAreas.Density4.selU_small_lt_two
import Submission.Work.LinnikAreas.Density4.exp_six_bound

namespace Work.LinnikAreas.Density4

open scoped BigOperators

/-- `Real.log (2 + Q) ≤ 2 · Real.log Q` for `Q ≥ 2` (from `2 + Q ≤ Q²`). -/
lemma log_add_two_le_two_mul_log (Q : ℝ) (hQ : 2 ≤ Q) :
    Real.log (2 + Q) ≤ 2 * Real.log Q := by
  have h2Qpos : (0 : ℝ) < 2 + Q := by linarith
  have hle : 2 + Q ≤ Q ^ 2 := by nlinarith
  calc Real.log (2 + Q) ≤ Real.log (Q ^ 2) := Real.log_le_log h2Qpos hle
    _ = 2 * Real.log Q := by rw [Real.log_pow]; norm_num

/-- Base case of the induction: `|selU Q - 1| ≤ c·(log(2+Q))^{-3}` for all `Q ≥ 1`.
For `Q ≥ 2` this follows from `selberg_U_decay` (`|selU x - 1| ≤ C(1+√log x)exp(-c√log x)`)
together with `log(2+Q) ≤ 2 log Q` and the elementary bound `t^7 e^{-ct} ≤ c^{-7}·7!` (from
`e^u ≥ u^7/7!`); for `1 ≤ Q < 2` one has `⌊Q⌋₊ = 1` and hence `selU Q = log Q`, so
`|selU Q - 1| ≤ 1 ≤ (log 4)^3·(log(2+Q))^{-3}`. -/
theorem selU_sub_one_bound : ∃ c : ℝ, 0 < c ∧ ∀ Q : ℝ, 1 ≤ Q →
    |selU Q - 1| ≤ c * (Real.log (2 + Q)) ^ (-3 : ℤ) := by
  obtain ⟨c0, C, hc0, hC, hdecay⟩ := selberg_U_decay
  refine ⟨C * max (16 * 5040 / c0 ^ 7) 16 + (Real.log 4) ^ 3 + 1, ?_, ?_⟩
  · -- positivity of the constant
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have hMpos : 0 < max (16 * 5040 / c0 ^ 7) 16 :=
      lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hCM : 0 < C * max (16 * 5040 / c0 ^ 7) 16 := mul_pos hC hMpos
    have hlog4c : 0 < (Real.log 4) ^ 3 := pow_pos hlog4 3
    linarith
  · intro Q hQ
    rcases lt_or_ge Q 2 with hQ2 | hQ2
    · -- small case `1 ≤ Q < 2`
      have hs := selU_small_lt_two Q hQ hQ2
      have hlog2Q : 0 < Real.log (2 + Q) := Real.log_pos (by linarith)
      have hgpos : 0 < (Real.log (2 + Q)) ^ (-3 : ℤ) := by
        rw [show (-3 : ℤ) = -(3 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
        exact inv_pos.mpr (pow_pos hlog2Q 3)
      have hc' : (Real.log 4) ^ 3
          ≤ C * max (16 * 5040 / c0 ^ 7) 16 + (Real.log 4) ^ 3 + 1 := by
        have hMpos : 0 < max (16 * 5040 / c0 ^ 7) 16 :=
          lt_of_lt_of_le (by norm_num) (le_max_right _ _)
        have : (0 : ℝ) ≤ C * max (16 * 5040 / c0 ^ 7) 16 := (mul_pos hC hMpos).le
        linarith
      calc |selU Q - 1|
          ≤ (Real.log 4) ^ 3 * (Real.log (2 + Q)) ^ (-3 : ℤ) := hs
        _ ≤ (C * max (16 * 5040 / c0 ^ 7) 16 + (Real.log 4) ^ 3 + 1)
              * (Real.log (2 + Q)) ^ (-3 : ℤ) :=
            mul_le_mul_of_nonneg_right hc' hgpos.le
    · -- large case `Q ≥ 2`
      have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
      set t : ℝ := Real.sqrt (Real.log Q) with ht_def
      have ht : 0 < t := by rw [ht_def]; exact Real.sqrt_pos.mpr hlogQ
      have ht6eq : t ^ 6 = (Real.log Q) ^ 3 := by
        rw [show t ^ 6 = (t ^ 2) ^ 3 by ring, ht_def, Real.sq_sqrt hlogQ.le]
      have hkey : Real.log (2 + Q) ≤ 2 * Real.log Q := log_add_two_le_two_mul_log Q hQ2
      have hlog2Q : 0 < Real.log (2 + Q) := Real.log_pos (by linarith)
      have hcube : (Real.log (2 + Q)) ^ 3 ≤ 8 * t ^ 6 := by
        have h1 : (Real.log (2 + Q)) ^ 3 ≤ (2 * Real.log Q) ^ 3 :=
          pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hkey 3
        have h2 : (2 * Real.log Q) ^ 3 = 8 * t ^ 6 := by rw [ht6eq]; ring
        linarith
      have hMpos : 0 < max (16 * 5040 / c0 ^ 7) 16 :=
        lt_of_lt_of_le (by norm_num) (le_max_right _ _)
      have hlo : 1 / (8 * t ^ 6) ≤ (Real.log (2 + Q)) ^ (-3 : ℤ) := by
        have hg_eq : (Real.log (2 + Q)) ^ (-3 : ℤ) = ((Real.log (2 + Q)) ^ 3)⁻¹ := by
          rw [show (-3 : ℤ) = -(3 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
        rw [hg_eq]
        simpa [one_div] using one_div_le_one_div_of_le (pow_pos hlog2Q 3) hcube
      have hgpos : 0 ≤ (Real.log (2 + Q)) ^ (-3 : ℤ) := by
        rw [show (-3 : ℤ) = -(3 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
        exact (inv_pos.mpr (pow_pos hlog2Q 3)).le
      have hexp := exp_six_bound hc0 t ht.le
      have hbase : (1 + t) * Real.exp (-(c0 * t))
          ≤ max (16 * 5040 / c0 ^ 7) 16 / (8 * t ^ 6) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 8 * t ^ 6)]
        have he : (1 + t) * Real.exp (-(c0 * t)) * (8 * t ^ 6)
            = 8 * t ^ 6 * (1 + t) * Real.exp (-(c0 * t)) := by ring
        rw [he]; exact hexp
      have hstep : C * (1 + t) * Real.exp (-(c0 * t))
          ≤ C * max (16 * 5040 / c0 ^ 7) 16 / (8 * t ^ 6) := by
        have h1 := mul_le_mul_of_nonneg_left hbase hC.le
        calc C * (1 + t) * Real.exp (-(c0 * t))
            = C * ((1 + t) * Real.exp (-(c0 * t))) := by ring
          _ ≤ C * (max (16 * 5040 / c0 ^ 7) 16 / (8 * t ^ 6)) := h1
          _ = C * max (16 * 5040 / c0 ^ 7) 16 / (8 * t ^ 6) := by ring
      have hdec := hdecay Q hQ2
      rw [← ht_def] at hdec
      have hCM_nn : 0 ≤ C * max (16 * 5040 / c0 ^ 7) 16 := (mul_pos hC hMpos).le
      have hc' : C * max (16 * 5040 / c0 ^ 7) 16
          ≤ C * max (16 * 5040 / c0 ^ 7) 16 + (Real.log 4) ^ 3 + 1 := by
        have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
        nlinarith [pow_pos hlog4 3]
      calc |selU Q - 1|
          ≤ C * (1 + t) * Real.exp (-(c0 * t)) := hdec
        _ ≤ C * max (16 * 5040 / c0 ^ 7) 16 / (8 * t ^ 6) := hstep
        _ = C * max (16 * 5040 / c0 ^ 7) 16 * (1 / (8 * t ^ 6)) := by ring
        _ ≤ C * max (16 * 5040 / c0 ^ 7) 16 * (Real.log (2 + Q)) ^ (-3 : ℤ) :=
            mul_le_mul_of_nonneg_left hlo hCM_nn
        _ ≤ (C * max (16 * 5040 / c0 ^ 7) 16 + (Real.log 4) ^ 3 + 1)
              * (Real.log (2 + Q)) ^ (-3 : ℤ) :=
            mul_le_mul_of_nonneg_right hc' hgpos

end Work.LinnikAreas.Density4
