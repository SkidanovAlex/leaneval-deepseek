import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Analysis.PertCrux

set_option linter.unusedVariables false

/-- Elementary logarithmic bound: `log x ≤ x/64 + log 64 - 1` for `x > 0`.
This is the standard `log y ≤ y - 1` applied to `y = x/64`. -/
private lemma log_le_div_add (x : ℝ) (hx : 0 < x) :
    Real.log x ≤ x / 64 + Real.log 64 - 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < x / 64 by positivity)
  have h2 : Real.log (x / 64) = Real.log x - Real.log 64 := by
    rw [Real.log_div (ne_of_gt hx) (by norm_num)]
  rw [h2] at h
  linarith

/-- Existence of a scale `Lam`, large compared with the input data, dominating the
logarithmic term `32 · CW · (2 + log(Ξ' + 3 Lam + MK + 5 CW + 4))`.
Since `log` grows slower than any positive multiple of `Lam`, a suitable
`Lam = M · T` with `M` the maximum of the data and `T ≈ 64 log M` works. -/
theorem scale_data {Ξ' MK CW Rgl : ℝ} (hΞ' : 1 ≤ Ξ') (hMK : 0 ≤ MK) (hCW : 0 ≤ CW)
    (hRgl : 0 ≤ Rgl) :
    ∃ Lam : ℝ, 64 ≤ Lam ∧ Ξ' ≤ Lam ∧ MK ≤ Lam ∧ CW ≤ Lam ∧ Rgl ≤ Lam / 8 ∧
      32 * CW * (2 + Real.log (Ξ' + 3 * Lam + MK + 5 * CW + 4)) ≤ Lam := by
  have hlog64 : (0:ℝ) ≤ Real.log 64 := Real.log_nonneg (by norm_num)
  have hlog11 : (0:ℝ) ≤ Real.log 11 := Real.log_nonneg (by norm_num)
  set M : ℝ := max (max (max 64 Ξ') MK) (max CW (8 * Rgl)) with hMdef
  set T : ℝ := 64 * (2 + Real.log 11 + Real.log M + Real.log 64) with hTdef
  have hM64 : (64:ℝ) ≤ M := by
    rw [hMdef]
    exact le_trans (le_trans (le_max_left 64 Ξ') (le_max_left (max 64 Ξ') MK))
      (le_max_left _ _)
  have hMΞ : Ξ' ≤ M := by
    rw [hMdef]
    exact le_trans (le_trans (le_max_right 64 Ξ') (le_max_left (max 64 Ξ') MK))
      (le_max_left _ _)
  have hMMK : MK ≤ M := by
    rw [hMdef]
    exact le_trans (le_max_right (max 64 Ξ') MK) (le_max_left _ _)
  have hMCW : CW ≤ M := by
    rw [hMdef]
    exact le_trans (le_max_left CW (8 * Rgl)) (le_max_right _ _)
  have hMRgl : 8 * Rgl ≤ M := by
    rw [hMdef]
    exact le_trans (le_max_right CW (8 * Rgl)) (le_max_right _ _)
  have hM0 : (0:ℝ) ≤ M := le_trans (by norm_num) hM64
  have hM1 : (1:ℝ) ≤ M := le_trans (by norm_num) hM64
  have hlogM : (0:ℝ) ≤ Real.log M := Real.log_nonneg hM1
  have hT1 : (1:ℝ) ≤ T := by
    rw [hTdef]; nlinarith [hlogM, hlog11, hlog64]
  have hT0 : (0:ℝ) < T := lt_of_lt_of_le (by norm_num) hT1
  have hMT : M ≤ M * T := le_mul_of_one_le_right hM0 hT1
  refine ⟨M * T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := mul_le_mul hM64 hT1 (by norm_num : (0:ℝ) ≤ 1) hM0
    simpa using this
  · exact le_trans hMΞ hMT
  · exact le_trans hMMK hMT
  · exact le_trans hMCW hMT
  · have h1 : Rgl ≤ M / 8 := by linarith
    have h2 : M / 8 ≤ M * T / 8 := div_le_div_of_nonneg_right hMT (by norm_num)
    linarith
  · have hinner_pos : (0:ℝ) < Ξ' + 3 * (M * T) + MK + 5 * CW + 4 := by
      nlinarith [hΞ', hMK, hCW, hM64, hT1]
    have hinner_le : Ξ' + 3 * (M * T) + MK + 5 * CW + 4 ≤ 11 * (M * T) := by
      nlinarith [hMΞ, hMMK, hMCW, hM64, hMT]
    have hlog_inner : Real.log (Ξ' + 3 * (M * T) + MK + 5 * CW + 4)
        ≤ Real.log (11 * (M * T)) := Real.log_le_log hinner_pos hinner_le
    have hstep1 : 32 * CW * (2 + Real.log (Ξ' + 3 * (M * T) + MK + 5 * CW + 4))
        ≤ 32 * M * (2 + Real.log (11 * (M * T))) := by
      have h1 : 32 * CW ≤ 32 * M := by linarith [hMCW]
      have h2 : 2 + Real.log (Ξ' + 3 * (M * T) + MK + 5 * CW + 4)
          ≤ 2 + Real.log (11 * (M * T)) := by linarith
      have hc : (0:ℝ) ≤ 2 + Real.log (Ξ' + 3 * (M * T) + MK + 5 * CW + 4) := by
        have : (0:ℝ) ≤ Real.log (Ξ' + 3 * (M * T) + MK + 5 * CW + 4) :=
          Real.log_nonneg (by linarith [hΞ', hMK, hCW, hM64, hT1])
        linarith
      exact mul_le_mul h1 h2 hc (by linarith [hM0])
    have hlog11MT : Real.log (11 * (M * T)) = Real.log 11 + Real.log M + Real.log T := by
      rw [Real.log_mul (by norm_num : (11:ℝ) ≠ 0) (by positivity : M * T ≠ 0)]
      rw [Real.log_mul (ne_of_gt (lt_of_lt_of_le (by norm_num) hM64)) (ne_of_gt hT0)]
      ring
    have hTlog : Real.log T ≤ T / 64 + Real.log 64 - 1 := log_le_div_add T hT0
    have hfinal : 2 + Real.log 11 + Real.log M + Real.log T ≤ T / 32 := by
      nlinarith [hTlog, hTdef, hlog11, hlogM, hlog64]
    have hstep2 : 32 * M * (2 + Real.log (11 * (M * T))) ≤ M * T := by
      rw [hlog11MT]
      have := mul_le_mul_of_nonneg_left hfinal (by positivity : (0:ℝ) ≤ 32 * M)
      have heq : 32 * M * (T / 32) = M * T := by ring
      linarith [this, heq]
    linarith [hstep1, hstep2]

end Work.Analysis.PertCrux
