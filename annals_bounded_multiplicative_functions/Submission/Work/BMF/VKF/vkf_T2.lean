import Mathlib
import Submission.Work.BMF.VKF.defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VKF

/-- The Taylor-remainder term of Ford's Lemma 5.1 is dominated by the target bound: for
`2 ≤ N ≤ t`, `λ = log t / log N ≥ 13/5`, `5λ+1 ≤ k ≤ 5λ+2`, `M ≤ 2N^{2/5}` and
`log N ≥ dK0·λ² = 300(1+sK)λ²`,

  `t·(M·M)^{k+1}/(k·N^k) ≤ dC·N^{1-1/(dD·λ²)}`.

Route: `t = N^λ` (from `λ = log t/log N`), so the left side is
`≤ 2^{2k+2}N^{λ+4(k+1)/5-k}/k` with exponent `λ+0.8-0.2k ≤ 0.6`; hence it suffices that
`(2k+2)log 2 ≤ (0.4 - 1/(dD·λ²))·log N`, which follows from
`(10λ+6)log 2 ≤ 7λ+5 ≤ 90λ² ≤ 0.3·dK0·λ² ≤ 0.3·log N` for `λ ≥ 13/5`. -/
theorem vkf_T2 (N t M lam : ℝ) (k : ℕ) (hN : 2 ≤ N) (hNt : N ≤ t)
    (hlamdef : lam = Real.log t / Real.log N) (hlam : 13 / 5 ≤ lam)
    (hk1 : 5 * lam + 1 ≤ (k : ℝ)) (hk2 : (k : ℝ) ≤ 5 * lam + 2)
    (hM0 : 0 ≤ M) (hM : M ≤ 2 * N ^ ((2 : ℝ) / 5))
    (hlogN : Work.BMF.VKF.dK0 * lam ^ 2 ≤ Real.log N) :
    t * (M * M) ^ (k + 1) / ((k : ℝ) * N ^ k)
      ≤ Work.BMF.VKF.dC * N ^ (1 - 1 / (Work.BMF.VKF.dD * lam ^ 2)) := by
  have hN1 : 1 < N := by linarith
  have hNpos : 0 < N := by linarith
  have hN0 : (0 : ℝ) ≤ N := hNpos.le
  have hlogNpos : 0 < Real.log N := Real.log_pos hN1
  have htpos : 0 < t := by linarith
  -- `t = N^λ`
  have ht : t = N ^ lam := by
    have hlogt : Real.log t = lam * Real.log N := by
      rw [hlamdef, div_mul_cancel₀]
      exact ne_of_gt hlogNpos
    rw [← Real.exp_log htpos, hlogt, Real.rpow_def_of_pos hNpos]
    congr 1
    ring
  rw [ht]
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by linarith
  have hkpos : 0 < (k : ℝ) := by linarith
  -- `(M·M)^{k+1} ≤ 4^{k+1}·N^{4(k+1)/5}`
  have hMM : (M * M) ^ (k + 1) ≤ 4 ^ (k + 1) * N ^ (4 * ((k : ℝ) + 1) / 5) := by
    have hpp : N ^ ((2 : ℝ) / 5) * N ^ ((2 : ℝ) / 5) = N ^ ((4 : ℝ) / 5) := by
      rw [← Real.rpow_add hNpos]
      norm_num
    have hMMA : M * M ≤ 4 * N ^ ((4 : ℝ) / 5) := by
      calc M * M ≤ (2 * N ^ ((2 : ℝ) / 5)) * (2 * N ^ ((2 : ℝ) / 5)) :=
            mul_le_mul hM hM hM0 (by positivity)
        _ = 4 * N ^ ((4 : ℝ) / 5) := by
            rw [show (2 * N ^ ((2 : ℝ) / 5)) * (2 * N ^ ((2 : ℝ) / 5))
                  = 4 * (N ^ ((2 : ℝ) / 5) * N ^ ((2 : ℝ) / 5)) by ring, hpp]
    have hpow : (N ^ ((4 : ℝ) / 5)) ^ (k + 1) = N ^ (4 * ((k : ℝ) + 1) / 5) := by
      rw [← Real.rpow_natCast (N ^ ((4 : ℝ) / 5)) (k + 1), ← Real.rpow_mul hNpos.le]
      congr 1
      push_cast
      ring
    calc (M * M) ^ (k + 1) ≤ (4 * N ^ ((4 : ℝ) / 5)) ^ (k + 1) :=
          pow_le_pow_left₀ (mul_nonneg hM0 hM0) hMMA _
      _ = 4 ^ (k + 1) * (N ^ ((4 : ℝ) / 5)) ^ (k + 1) := mul_pow _ _ _
      _ = 4 ^ (k + 1) * N ^ (4 * ((k : ℝ) + 1) / 5) := by rw [hpow]
  -- combine the powers of `N` in the denominator
  have hrw : N ^ lam * (4 ^ (k + 1) * N ^ (4 * ((k : ℝ) + 1) / 5)) / ((k : ℝ) * N ^ k)
      = 4 ^ (k + 1) * N ^ (lam + 4 * ((k : ℝ) + 1) / 5 - (k : ℝ)) / (k : ℝ) := by
    rw [← Real.rpow_natCast N k]
    have h1 : N ^ lam * (4 ^ (k + 1) * N ^ (4 * ((k : ℝ) + 1) / 5))
        = 4 ^ (k + 1) * (N ^ lam * N ^ (4 * ((k : ℝ) + 1) / 5)) := by ring
    rw [h1, ← Real.rpow_add hNpos]
    have h2 : 4 ^ (k + 1) * N ^ (lam + 4 * ((k : ℝ) + 1) / 5) / ((k : ℝ) * N ^ (k : ℝ))
        = 4 ^ (k + 1) * (N ^ (lam + 4 * ((k : ℝ) + 1) / 5) / N ^ (k : ℝ)) / (k : ℝ) := by
      field_simp
    rw [h2, ← Real.rpow_sub hNpos]
  -- the exponent is at most `3/5`
  have hexp3 : lam + 4 * ((k : ℝ) + 1) / 5 - (k : ℝ) ≤ 3 / 5 := by linarith
  have h4pow : (4 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (2 * k + 2) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    rfl
  -- `2^{2k+2} ≤ dC·N^{1/3}`
  have hstep4 : (2 : ℝ) ^ (2 * k + 2) ≤ Work.BMF.VKF.dC * N ^ ((1 : ℝ) / 3) := by
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2le : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hsK : 0 ≤ Work.BMF.VKF.sK := Work.BMF.VKF.sK_nonneg
    have hexp : Real.log 2 * ((2 * k + 2 : ℕ) : ℝ) ≤
        (1000 + 100 * Work.BMF.VKF.sK) + Real.log N * (1 / 3) := by
      have h1 : Real.log 2 * ((2 * k + 2 : ℕ) : ℝ) ≤ Real.log 2 * (10 * lam + 6) := by
        have hle : ((2 * k + 2 : ℕ) : ℝ) ≤ 10 * lam + 6 := by push_cast; linarith
        exact mul_le_mul_of_nonneg_left hle hlog2pos.le
      have h2 : Real.log 2 * (10 * lam + 6) ≤ 10 * lam + 6 := by
        have hnn : (0 : ℝ) ≤ 10 * lam + 6 := by linarith
        have h := mul_le_mul_of_nonneg_right hlog2le hnn
        linarith
      have h3 : 10 * lam + 6 ≤ 100 * lam ^ 2 := by nlinarith [hlam]
      have hlogN' : 300 * (1 + Work.BMF.VKF.sK) * lam ^ 2 ≤ Real.log N := hlogN
      have h5 : 100 * (1 + Work.BMF.VKF.sK) * lam ^ 2 ≤ Real.log N * (1 / 3) := by
        nlinarith [hlogN']
      have h6 : 100 * lam ^ 2 ≤ 100 * (1 + Work.BMF.VKF.sK) * lam ^ 2 := by
        nlinarith [hsK, sq_nonneg lam]
      linarith
    have hleft : (2 : ℝ) ^ (2 * k + 2) = Real.exp (Real.log 2 * ((2 * k + 2 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast (2 : ℝ) (2 * k + 2),
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hright : Work.BMF.VKF.dC * N ^ ((1 : ℝ) / 3) =
        Real.exp ((1000 + 100 * Work.BMF.VKF.sK) + Real.log N * (1 / 3)) := by
      rw [Work.BMF.VKF.dC]
      rw [Real.rpow_def_of_pos hNpos]
      rw [← Real.exp_add]
    rw [hleft, hright]
    exact Real.exp_le_exp.mpr hexp
  -- `14/15 ≤ 1 - 1/(dD·λ²)`
  have hstep6 : (14 : ℝ) / 15 ≤ 1 - 1 / (Work.BMF.VKF.dD * lam ^ 2) := by
    have hD : Work.BMF.VKF.dD = (10 : ℝ) ^ 9 := rfl
    have hlam2 : (169 : ℝ) / 25 ≤ lam ^ 2 := by nlinarith [hlam]
    have hDlam : (15 : ℝ) ≤ Work.BMF.VKF.dD * lam ^ 2 := by rw [hD]; nlinarith [hlam2]
    have hle : 1 / (Work.BMF.VKF.dD * lam ^ 2) ≤ 1 / 15 :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 15) hDlam
    linarith
  calc N ^ lam * (M * M) ^ (k + 1) / ((k : ℝ) * N ^ k)
      ≤ N ^ lam * (4 ^ (k + 1) * N ^ (4 * ((k : ℝ) + 1) / 5)) / ((k : ℝ) * N ^ k) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hMM (Real.rpow_nonneg hN0 lam))
          (mul_nonneg hkpos.le (pow_nonneg hN0 _))
    _ = 4 ^ (k + 1) * N ^ (lam + 4 * ((k : ℝ) + 1) / 5 - (k : ℝ)) / (k : ℝ) := hrw
    _ ≤ 4 ^ (k + 1) * N ^ ((3 : ℝ) / 5) / (k : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hN1.le hexp3)
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _))
          hkpos.le
    _ ≤ 4 ^ (k + 1) * N ^ ((3 : ℝ) / 5) := by
        rw [div_le_iff₀ hkpos]
        exact le_mul_of_one_le_right (a := 4 ^ (k + 1) * N ^ ((3 : ℝ) / 5)) (by positivity) hk1'
    _ = (2 : ℝ) ^ (2 * k + 2) * N ^ ((3 : ℝ) / 5) := by rw [h4pow]
    _ ≤ (Work.BMF.VKF.dC * N ^ ((1 : ℝ) / 3)) * N ^ ((3 : ℝ) / 5) :=
        mul_le_mul_of_nonneg_right hstep4 (Real.rpow_nonneg hN0 ((3 : ℝ) / 5))
    _ = Work.BMF.VKF.dC * N ^ ((14 : ℝ) / 15) := by
        rw [mul_assoc, ← Real.rpow_add hNpos]
        norm_num
    _ ≤ Work.BMF.VKF.dC * N ^ (1 - 1 / (Work.BMF.VKF.dD * lam ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hN1.le hstep6) Work.BMF.VKF.dC_pos.le

end Work.BMF.VKF
