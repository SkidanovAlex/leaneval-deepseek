import Mathlib
import Submission.Work.BMF.VKdenom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open Real

/-- `L ^ (5/4)` with a negative base is negative (the exponent `5/4` lies in `(1, 3/2)`,
where `cos (y π) < 0`). -/
lemma rpow_five_four_neg_of_neg {L : ℝ} (hL : L < 0) : L ^ (5 / 4 : ℝ) < 0 := by
  rw [Real.rpow_def_of_neg hL]
  have hcos : Real.cos ((5 / 4 : ℝ) * π) < 0 := by
    have hh : (5 / 4 : ℝ) * π = 5 * π / 4 := by ring
    rw [hh]
    exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) hcos

theorem VKd_three_exp_le (L : ℝ)
    (h3 : Real.log 3 ≤ L ^ (5 / 4 : ℝ))
    (h2 : Real.log 2 ≤ (3 / 4) * Real.log L)
    (hlog : 2 * (Real.log L) ^ (1 / 3 : ℝ) ≤ L ^ (1 / 15 : ℝ)) :
    Work.BMF.VKd (3 * Real.exp (L ^ (5 / 4 : ℝ))) ≤ L ^ (9 / 10 : ℝ) := by
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  -- `h3` forces `L > 0` (a nonpositive base makes `L ^ (5/4) ≤ 0 < log 3`).
  have hLpos : 0 < L := by
    by_contra h
    have hle : L ≤ 0 := not_lt.mp h
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hneg : L ^ (5 / 4 : ℝ) < 0 := rpow_five_four_neg_of_neg hlt
      linarith
    · subst heq
      rw [Real.zero_rpow (by norm_num : (5 / 4 : ℝ) ≠ 0)] at h3
      linarith
  -- `h2` forces `log L > 0`, hence `L > 1`.
  have hlogL_pos : 0 < Real.log L := by
    have : 0 < (3 / 4) * Real.log L := lt_of_lt_of_le (Real.log_pos (by norm_num)) h2
    nlinarith
  have hL1 : 1 < L := (Real.log_pos_iff hLpos.le).mp hlogL_pos
  set X : ℝ := L ^ (5 / 4 : ℝ) with hX
  have hXpos : 0 < X := by rw [hX]; exact Real.rpow_pos_of_pos hLpos _
  have hlogy : Real.log (3 * Real.exp X) = Real.log 3 + X := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero X), Real.log_exp]
  have hlogy_le : Real.log (3 * Real.exp X) ≤ 2 * X := by
    rw [hlogy]; linarith
  have hlogy_ge1 : 1 ≤ Real.log (3 * Real.exp X) := by
    rw [hlogy]; linarith [Work.BMF.one_le_log_three, hXpos]
  -- First factor: `(log y)^{2/3} ≤ 2^{2/3} L^{5/6}`.
  have hA : (Real.log (3 * Real.exp X)) ^ (2 / 3 : ℝ) ≤ (2 : ℝ) ^ (2 / 3 : ℝ) * L ^ (5 / 6 : ℝ) := by
    have h1 : (Real.log (3 * Real.exp X)) ^ (2 / 3 : ℝ) ≤ (2 * X) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hlogy_le (by norm_num)
    have h2 : (2 * X) ^ (2 / 3 : ℝ) = (2 : ℝ) ^ (2 / 3 : ℝ) * X ^ (2 / 3 : ℝ) :=
      Real.mul_rpow (by norm_num) hXpos.le
    have h3'' : X ^ (2 / 3 : ℝ) = L ^ (5 / 6 : ℝ) := by
      rw [hX, ← Real.rpow_mul hLpos.le]
      norm_num
    rwa [h2, h3''] at h1
  -- Second factor: `(log log y)^{1/3} ≤ 2^{1/3} (log L)^{1/3}`.
  have hB : (Real.log (Real.log (3 * Real.exp X))) ^ (1 / 3 : ℝ) ≤
      (2 : ℝ) ^ (1 / 3 : ℝ) * (Real.log L) ^ (1 / 3 : ℝ) := by
    have hloglog_le : Real.log (Real.log (3 * Real.exp X)) ≤ 2 * Real.log L := by
      have hpos : 0 < Real.log (3 * Real.exp X) := by linarith
      have h := Real.log_le_log hpos hlogy_le
      rw [Real.log_mul (by norm_num) (ne_of_gt hXpos)] at h
      have hlogX : Real.log X = (5 / 4) * Real.log L := by rw [hX, Real.log_rpow hLpos]
      rw [hlogX] at h
      linarith
    have hnn : 0 ≤ Real.log (Real.log (3 * Real.exp X)) := Real.log_nonneg hlogy_ge1
    have h1 := Real.rpow_le_rpow hnn hloglog_le (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have h2' : (2 * Real.log L) ^ (1 / 3 : ℝ) = (2 : ℝ) ^ (1 / 3 : ℝ) * (Real.log L) ^ (1 / 3 : ℝ) :=
      Real.mul_rpow (by norm_num) (le_of_lt hlogL_pos)
    rwa [h2'] at h1
  have h2pow : (2 : ℝ) ^ (2 / 3 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hc_nonneg : 0 ≤ (Real.log (Real.log (3 * Real.exp X))) ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg (Real.log_nonneg hlogy_ge1) _
  have hb_nonneg : 0 ≤ (2 : ℝ) ^ (2 / 3 : ℝ) * L ^ (5 / 6 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hLpos.le _)
  have hstep : ((2 : ℝ) ^ (2 / 3 : ℝ) * L ^ (5 / 6 : ℝ)) *
        ((2 : ℝ) ^ (1 / 3 : ℝ) * (Real.log L) ^ (1 / 3 : ℝ))
      = ((2 : ℝ) ^ (2 / 3 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ)) *
        (L ^ (5 / 6 : ℝ) * (Real.log L) ^ (1 / 3 : ℝ)) := by ring
  calc Work.BMF.VKd (3 * Real.exp X)
      = (Real.log (3 * Real.exp X)) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log (3 * Real.exp X))) ^ (1 / 3 : ℝ) := by
        rw [Work.BMF.VKd_def]
    _ ≤ ((2 : ℝ) ^ (2 / 3 : ℝ) * L ^ (5 / 6 : ℝ)) *
          ((2 : ℝ) ^ (1 / 3 : ℝ) * (Real.log L) ^ (1 / 3 : ℝ)) :=
        mul_le_mul hA hB hc_nonneg hb_nonneg
    _ = 2 * L ^ (5 / 6 : ℝ) * (Real.log L) ^ (1 / 3 : ℝ) := by rw [hstep, h2pow]; ring
    _ = L ^ (5 / 6 : ℝ) * (2 * (Real.log L) ^ (1 / 3 : ℝ)) := by ring
    _ ≤ L ^ (5 / 6 : ℝ) * L ^ (1 / 15 : ℝ) :=
        mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hLpos.le _)
    _ = L ^ (9 / 10 : ℝ) := by rw [← Real.rpow_add hLpos]; norm_num

end Work.BMF.liouville
