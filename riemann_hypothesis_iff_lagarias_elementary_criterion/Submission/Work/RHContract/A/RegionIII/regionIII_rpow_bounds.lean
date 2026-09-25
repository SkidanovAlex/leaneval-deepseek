import Mathlib
import Submission.Work.RHContract.A.RegionIII.caRegionIIIDefs

namespace Work.RHContract.A.RegionIII

theorem regionIII_rpow_bounds (ε : ℝ) (hξ : (10 : ℝ) ^ 8 ≤ Work.RHContract.A.RegionIII.caXiR ε) :
    Work.RHContract.A.RegionIII.caL ε ≤ 8 * Work.RHContract.A.RegionIII.caXiR ε ^ (1 / 8 : ℝ)
      ∧ (100 : ℝ) ≤ Work.RHContract.A.RegionIII.caXiR ε ^ (1 / 4 : ℝ)
      ∧ (1000 : ℝ) ≤ Work.RHContract.A.RegionIII.caXiR ε ^ (3 / 8 : ℝ)
      ∧ (10 ^ 6 : ℝ) ≤ Work.RHContract.A.RegionIII.caXiR ε ^ (3 / 4 : ℝ)
      ∧ (10 : ℝ) ≤ (Work.RHContract.A.RegionIII.caN ε : ℝ) ^ (1 / 4 : ℝ)
      ∧ 17.7 * Real.sqrt (Work.RHContract.A.RegionIII.caXiR ε) ≤ (Work.RHContract.A.RegionIII.caN ε : ℝ) ^ (5 / 4 : ℝ)
      ∧ 198.8 * Real.sqrt (Work.RHContract.A.RegionIII.caXiR ε) ≤ (Work.RHContract.A.RegionIII.caN ε : ℝ) ^ (3 / 2 : ℝ) := by
  have hξpos : (0 : ℝ) < caXiR ε := lt_of_lt_of_le (by norm_num) hξ
  have hξn : (100000000 : ℝ) ≤ caXiR ε := by have h := hξ; norm_num at h; exact h
  -- generic numeric helpers
  have h25 : (1.77 : ℝ) ≤ (5 / 2 : ℝ) ^ (5 / 8 : ℝ) := by
    rw [← Real.rpow_le_rpow_iff (x := (1.77 : ℝ)) (y := (5 / 2 : ℝ) ^ (5 / 8 : ℝ))
      (z := (8 : ℝ)) (by norm_num) (Real.rpow_nonneg (by norm_num) _) (by norm_num)]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5 / 2) (5 / 8) (8)]
    norm_num
  have h198 : (1.988 : ℝ) ≤ (5 / 2 : ℝ) ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_le_rpow_iff (x := (1.988 : ℝ)) (y := (5 / 2 : ℝ) ^ (3 / 4 : ℝ))
      (z := (4 : ℝ)) (by norm_num) (Real.rpow_nonneg (by norm_num) _) (by norm_num)]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5 / 2) (3 / 4) (4)]
    norm_num
  have hξ8 : (10 : ℝ) ≤ caXiR ε ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_le_rpow_iff (x := (10 : ℝ)) (y := caXiR ε ^ (1 / 8 : ℝ))
      (z := (8 : ℝ)) (by norm_num) (Real.rpow_nonneg (le_of_lt hξpos) _) (by norm_num)]
    rw [← Real.rpow_mul (le_of_lt hξpos) (1 / 8) (8)]
    norm_num
    exact hξn
  have hξ4 : (100 : ℝ) ≤ caXiR ε ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_le_rpow_iff (x := (100 : ℝ)) (y := caXiR ε ^ (1 / 4 : ℝ))
      (z := (4 : ℝ)) (by norm_num) (Real.rpow_nonneg (le_of_lt hξpos) _) (by norm_num)]
    rw [← Real.rpow_mul (le_of_lt hξpos) (1 / 4) (4)]
    norm_num
    exact hξn
  have hNgt : Real.sqrt (2.5 * caXiR ε) < (caN ε : ℝ) := by
    rw [caN_eq, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- log bound
    rw [caL_eq]
    calc Real.log (caXiR ε) ≤ caXiR ε ^ (1 / 8 : ℝ) / (1 / 8 : ℝ) :=
          Real.log_le_rpow_div (le_of_lt hξpos) (by norm_num)
      _ = 8 * caXiR ε ^ (1 / 8 : ℝ) := by ring
  · -- 100 ≤ ξ^{1/4}
    rw [← Real.rpow_le_rpow_iff (x := (100 : ℝ)) (y := caXiR ε ^ (1 / 4 : ℝ))
      (z := (4 : ℝ)) (by norm_num) (Real.rpow_nonneg (le_of_lt hξpos) _) (by norm_num)]
    rw [← Real.rpow_mul (le_of_lt hξpos) (1 / 4) (4)]
    norm_num
    exact hξn
  · -- 1000 ≤ ξ^{3/8}
    rw [← Real.rpow_le_rpow_iff (x := (1000 : ℝ)) (y := caXiR ε ^ (3 / 8 : ℝ))
      (z := (8 / 3 : ℝ)) (by norm_num) (Real.rpow_nonneg (le_of_lt hξpos) _) (by norm_num)]
    rw [← Real.rpow_mul (le_of_lt hξpos) (3 / 8) (8 / 3)]
    norm_num
    exact hξn
  · -- 10^6 ≤ ξ^{3/4}
    rw [← Real.rpow_le_rpow_iff (x := (10 ^ 6 : ℝ)) (y := caXiR ε ^ (3 / 4 : ℝ))
      (z := (4 / 3 : ℝ)) (by norm_num) (Real.rpow_nonneg (le_of_lt hξpos) _) (by norm_num)]
    rw [← Real.rpow_mul (le_of_lt hξpos) (3 / 4) (4 / 3)]
    norm_num
    exact hξn
  · -- 10 ≤ n^{1/4}
    have hsq : (10 : ℝ) ^ 4 ≤ Real.sqrt (2.5 * caXiR ε) := by
      have h2 : (10 : ℝ) ^ 8 ≤ 2.5 * caXiR ε := by nlinarith [hξ]
      have h := Real.sqrt_le_sqrt h2
      have hs : Real.sqrt ((10 : ℝ) ^ 8) = (10 : ℝ) ^ 4 := by
        rw [show (10 : ℝ) ^ 8 = ((10 : ℝ) ^ 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rwa [hs] at h
    have hN4 : (10000 : ℝ) ≤ (caN ε : ℝ) := by
      have h := le_trans hsq (le_of_lt hNgt)
      norm_num at h ⊢
      exact h
    rw [← Real.rpow_le_rpow_iff (x := (10 : ℝ)) (y := (caN ε : ℝ) ^ (1 / 4 : ℝ))
      (z := (4 : ℝ)) (by norm_num) (Real.rpow_nonneg (by positivity) _) (by norm_num)]
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (caN ε : ℝ)) (1 / 4) (4)]
    norm_num
    exact_mod_cast hN4
  · -- 17.7 √ξ ≤ n^{5/4}
    have step1 : (Real.sqrt (2.5 * caXiR ε)) ^ (5 / 4 : ℝ) ≤ (caN ε : ℝ) ^ (5 / 4 : ℝ) :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) (le_of_lt hNgt) (by norm_num)
    have hsq : (Real.sqrt (2.5 * caXiR ε)) ^ (5 / 4 : ℝ)
        = (5 / 2 : ℝ) ^ (5 / 8 : ℝ) * caXiR ε ^ (1 / 8 : ℝ) * Real.sqrt (caXiR ε) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2.5 * caXiR ε) (1 / 2) (5 / 4)]
      norm_num
      rw [Real.mul_rpow (x := (5 / 2 : ℝ)) (by norm_num) (by positivity : (0 : ℝ) ≤ caXiR ε)]
      rw [show caXiR ε ^ (5 / 8 : ℝ) = caXiR ε ^ (1 / 2 : ℝ) * caXiR ε ^ (1 / 8 : ℝ) by
            rw [show (5 / 8 : ℝ) = 1 / 2 + 1 / 8 by norm_num, Real.rpow_add hξpos]]
      rw [Real.sqrt_eq_rpow]
      ring
    have key : 17.7 * Real.sqrt (caXiR ε)
        ≤ (5 / 2 : ℝ) ^ (5 / 8 : ℝ) * caXiR ε ^ (1 / 8 : ℝ) * Real.sqrt (caXiR ε) := by
      have hb : (1.77 : ℝ) * Real.sqrt (caXiR ε)
          ≤ (5 / 2 : ℝ) ^ (5 / 8 : ℝ) * Real.sqrt (caXiR ε) :=
        mul_le_mul_of_nonneg_right h25 (Real.sqrt_nonneg _)
      have hbnonneg : 0 ≤ (5 / 2 : ℝ) ^ (5 / 8 : ℝ) * Real.sqrt (caXiR ε) :=
        mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
      have hk := mul_le_mul hb hξ8 (by norm_num) hbnonneg
      have e1 : (1.77 : ℝ) * Real.sqrt (caXiR ε) * 10 = 17.7 * Real.sqrt (caXiR ε) := by ring
      have e2 : (5 / 2 : ℝ) ^ (5 / 8 : ℝ) * Real.sqrt (caXiR ε) * caXiR ε ^ (1 / 8 : ℝ)
          = (5 / 2 : ℝ) ^ (5 / 8 : ℝ) * caXiR ε ^ (1 / 8 : ℝ) * Real.sqrt (caXiR ε) := by ring
      rw [e1, e2] at hk
      exact hk
    calc 17.7 * Real.sqrt (caXiR ε)
          ≤ (5 / 2 : ℝ) ^ (5 / 8 : ℝ) * caXiR ε ^ (1 / 8 : ℝ) * Real.sqrt (caXiR ε) := key
      _ = (Real.sqrt (2.5 * caXiR ε)) ^ (5 / 4 : ℝ) := hsq.symm
      _ ≤ (caN ε : ℝ) ^ (5 / 4 : ℝ) := step1
  · -- 198.8 √ξ ≤ n^{3/2}
    have step1 : (Real.sqrt (2.5 * caXiR ε)) ^ (3 / 2 : ℝ) ≤ (caN ε : ℝ) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) (le_of_lt hNgt) (by norm_num)
    have hsq : (Real.sqrt (2.5 * caXiR ε)) ^ (3 / 2 : ℝ)
        = (5 / 2 : ℝ) ^ (3 / 4 : ℝ) * caXiR ε ^ (1 / 4 : ℝ) * Real.sqrt (caXiR ε) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2.5 * caXiR ε) (1 / 2) (3 / 2)]
      norm_num
      rw [Real.mul_rpow (x := (5 / 2 : ℝ)) (by norm_num) (by positivity : (0 : ℝ) ≤ caXiR ε)]
      rw [show caXiR ε ^ (3 / 4 : ℝ) = caXiR ε ^ (1 / 2 : ℝ) * caXiR ε ^ (1 / 4 : ℝ) by
            rw [show (3 / 4 : ℝ) = 1 / 2 + 1 / 4 by norm_num, Real.rpow_add hξpos]]
      rw [Real.sqrt_eq_rpow]
      ring
    have key : 198.8 * Real.sqrt (caXiR ε)
        ≤ (5 / 2 : ℝ) ^ (3 / 4 : ℝ) * caXiR ε ^ (1 / 4 : ℝ) * Real.sqrt (caXiR ε) := by
      have hb : (1.988 : ℝ) * Real.sqrt (caXiR ε)
          ≤ (5 / 2 : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (caXiR ε) :=
        mul_le_mul_of_nonneg_right h198 (Real.sqrt_nonneg _)
      have hbnonneg : 0 ≤ (5 / 2 : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (caXiR ε) :=
        mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
      have hk := mul_le_mul hb hξ4 (by norm_num) hbnonneg
      have e1 : (1.988 : ℝ) * Real.sqrt (caXiR ε) * 100 = 198.8 * Real.sqrt (caXiR ε) := by ring
      have e2 : (5 / 2 : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (caXiR ε) * caXiR ε ^ (1 / 4 : ℝ)
          = (5 / 2 : ℝ) ^ (3 / 4 : ℝ) * caXiR ε ^ (1 / 4 : ℝ) * Real.sqrt (caXiR ε) := by ring
      rw [e1, e2] at hk
      exact hk
    calc 198.8 * Real.sqrt (caXiR ε)
          ≤ (5 / 2 : ℝ) ^ (3 / 4 : ℝ) * caXiR ε ^ (1 / 4 : ℝ) * Real.sqrt (caXiR ε) := key
      _ = (Real.sqrt (2.5 * caXiR ε)) ^ (3 / 2 : ℝ) := hsq.symm
      _ ≤ (caN ε : ℝ) ^ (3 / 2 : ℝ) := step1

end Work.RHContract.A.RegionIII
