import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.logBogTBound` — the sharp `log T` row at the honest datum

With `D = dil v μ`, `L = log D⁻¹ ≥ 1` and `ε ≥ D^{1/1292}(1 + (156/323)L)`, the honest
momentum cutoff `T = 10⁶(1+L)/ε` satisfies

    `log T ≤ 56 + (1/1292)L`.

This is the sharpening of `Work.BoseBogFS.bogTLogLe` (which used `log(1+L) ≤ L` and only
reached `54 + (1293/1292)L`): the point is that the *same* factor `(1 + (156/323)L)` that
lowers `ε` cuts the numerator, so the two `(1/1292)L` terms cancel and only the
`L`-independent ratio `(1+L)/(1 + (156/323)L) ≤ 323/156` survives.  That ratio bound is the
key elementary input; the numeric constant `56` then costs only
`log(10⁶ · 323/156) ≤ log(3·10⁶) = log 3 + 6 log 10 ≤ 2 + 54 = 56`.
-/

namespace Work.BoseBogFS

/-- The `log T` row at the honest data, sharp form: for `L = log D⁻¹ ≥ 1` and
`ε ≥ D^{1/1292}(1 + (156/323)L)` one has `log(10⁶(1+L)/ε) ≤ 56 + (1/1292)L`. -/
theorem logBogTBound {D L eps : ℝ} (hD0 : 0 < D) (hL1 : 1 ≤ L)
    (hLdef : L = Real.log (1 / D)) (heps0 : 0 < eps)
    (hE3 : D ^ ((1 : ℝ) / 1292) * (1 + ((156 : ℝ) / 323) * L) ≤ eps) :
    Real.log (10 ^ 6 * (1 + L) / eps) ≤ 56 + (1 / 1292) * L := by
  -- positivity bookkeeping
  have hUpos : 0 < (1 + L : ℝ) := by linarith
  have hWpos : 0 < (1 + ((156 : ℝ) / 323) * L) := by
    have h1 : (0 : ℝ) < 156 / 323 := by norm_num
    have h2 : (0 : ℝ) < L := by linarith
    have h3 := mul_pos h1 h2
    linarith
  -- `log D = -L` and `log (D^{1/1292}) = -(1/1292)L`
  have hlogD : Real.log D = -L := by
    rw [hLdef, one_div, Real.log_inv]; ring
  have hBpos : 0 < D ^ ((1 : ℝ) / 1292) := Real.rpow_pos_of_pos hD0 _
  have hlogB : Real.log (D ^ ((1 : ℝ) / 1292)) = -((1 : ℝ) / 1292) * L := by
    rw [Real.log_rpow hD0, hlogD]; ring
  -- the lower bound on `log ε`
  have hlogeps : Real.log (D ^ ((1 : ℝ) / 1292) * (1 + ((156 : ℝ) / 323) * L)) ≤ Real.log eps :=
    Real.log_le_log (mul_pos hBpos hWpos) hE3
  have hlogDW : Real.log (D ^ ((1 : ℝ) / 1292) * (1 + ((156 : ℝ) / 323) * L))
      = -((1 : ℝ) / 1292) * L + Real.log (1 + ((156 : ℝ) / 323) * L) := by
    rw [Real.log_mul (ne_of_gt hBpos) (ne_of_gt hWpos), hlogB]
  -- split the logarithm of the cutoff
  have hlogmain : Real.log (10 ^ 6 * (1 + L) / eps)
      = Real.log ((10 : ℝ) ^ 6) + Real.log (1 + L) - Real.log eps := by
    rw [Real.log_div (by positivity) (ne_of_gt heps0),
        Real.log_mul (by norm_num) (ne_of_gt hUpos)]
  rw [hlogmain]
  have hstep : Real.log ((10 : ℝ) ^ 6) + Real.log (1 + L) - Real.log eps
      ≤ Real.log ((10 : ℝ) ^ 6) + Real.log (1 + L)
        - (-((1 : ℝ) / 1292) * L + Real.log (1 + ((156 : ℝ) / 323) * L)) := by
    linarith [hlogeps, hlogDW]
  have hcomb : Real.log ((10 : ℝ) ^ 6) + Real.log (1 + L)
        - (-((1 : ℝ) / 1292) * L + Real.log (1 + ((156 : ℝ) / 323) * L))
      = Real.log ((10 : ℝ) ^ 6 * (1 + L) / (1 + ((156 : ℝ) / 323) * L))
        + ((1 : ℝ) / 1292) * L := by
    rw [Real.log_div (by positivity) (ne_of_gt hWpos),
        Real.log_mul (by norm_num) (ne_of_gt hUpos)]
    ring
  -- the ratio `(1+L)/(1 + (156/323)L)` is bounded by `323/156`
  have hratio : (1 + L) / (1 + ((156 : ℝ) / 323) * L) ≤ 323 / 156 := by
    rw [div_le_iff₀ hWpos]
    have : ((323 : ℝ) / 156) * (1 + 156 / 323 * L) = 323 / 156 + L := by ring
    rw [this]; linarith
  have hbound : (10 : ℝ) ^ 6 * (1 + L) / (1 + ((156 : ℝ) / 323) * L)
      ≤ (10 : ℝ) ^ 6 * (323 / 156) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hratio (by norm_num)
  -- and `log(10⁶ · 323/156) ≤ 56`
  have h3 : Real.log ((10 : ℝ) ^ 6 * (323 / 156)) ≤ 56 := by
    have hle : (10 : ℝ) ^ 6 * (323 / 156) ≤ 3 * (10 : ℝ) ^ 6 := by norm_num
    have h1 : Real.log ((10 : ℝ) ^ 6 * (323 / 156)) ≤ Real.log (3 * (10 : ℝ) ^ 6) :=
      Real.log_le_log (by norm_num) hle
    have h2 : Real.log (3 * (10 : ℝ) ^ 6) = Real.log 3 + 6 * Real.log 10 := by
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
    rw [h2] at h1
    have h3a : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
    have h3b : Real.log 10 ≤ 9 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10); linarith
    linarith
  have hfin : Real.log ((10 : ℝ) ^ 6 * (1 + L) / (1 + ((156 : ℝ) / 323) * L)) ≤ 56 := by
    have := Real.log_le_log (by positivity) hbound
    linarith
  rw [hcomb] at hstep
  linarith

end Work.BoseBogFS
