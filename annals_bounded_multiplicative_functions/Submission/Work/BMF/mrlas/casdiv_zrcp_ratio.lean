import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.halasz_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

/-- **Mertens, upper form.** `exp (Zrcp t) ≤ exp C₀ · log t` for `t ≥ 11`, given
`|Zrcp t − log log t| ≤ C₀` there: `Zrcp t ≤ log log t + C₀` and `exp (log log t) = log t`. -/
private lemma exp_Zrcp_le_mul_log (C₀ : ℝ)
    (hMertens : ∀ t : ℝ, 11 ≤ t → |Work.BMF.Zrcp t - Real.log (Real.log t)| ≤ C₀)
    {t : ℝ} (ht : 11 ≤ t) :
    Real.exp (Work.BMF.Zrcp t) ≤ Real.exp C₀ * Real.log t := by
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have h := (abs_le.mp (hMertens t ht)).2
  have h2 : Work.BMF.Zrcp t ≤ Real.log (Real.log t) + C₀ := by linarith
  calc Real.exp (Work.BMF.Zrcp t) ≤ Real.exp (Real.log (Real.log t) + C₀) := Real.exp_le_exp.mpr h2
    _ = Real.exp C₀ * Real.log t := by rw [Real.exp_add, Real.exp_log hlogt, mul_comm]

/-- **Mertens, lower form.** `log t · exp (−C₀) ≤ exp (Zrcp t)` for `t ≥ 11`, given
`|Zrcp t − log log t| ≤ C₀` there: `log log t − C₀ ≤ Zrcp t`. -/
private lemma mul_exp_neg_le_exp_Zrcp (C₀ : ℝ)
    (hMertens : ∀ t : ℝ, 11 ≤ t → |Work.BMF.Zrcp t - Real.log (Real.log t)| ≤ C₀)
    {t : ℝ} (ht : 11 ≤ t) :
    Real.log t * Real.exp (-C₀) ≤ Real.exp (Work.BMF.Zrcp t) := by
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have h := (abs_le.mp (hMertens t ht)).1
  have h2 : Real.log (Real.log t) + (-C₀) ≤ Work.BMF.Zrcp t := by linarith
  have h3 : Real.exp (Real.log (Real.log t) + (-C₀)) ≤ Real.exp (Work.BMF.Zrcp t) :=
    Real.exp_le_exp.mpr h2
  rwa [Real.exp_add, Real.exp_log hlogt] at h3

/-- **Mertens (the `hypsupdiv` hypothesis for `r ≡ 1`), with the Mertens input as a parameter.**
Given `|Zrcp t − log log t| ≤ C₀` for `t ≥ 11`, we get for `2 ≤ y ≤ x`
`exp (Zrcp y) ≤ C exp (Zrcp x) (log y / log x)`: the Mertens input gives
`Zrcp x − Zrcp y ≥ log (log x / log y) − 2C₀` when `y ≥ 11`, and the remaining cases
`x < 11` and `2 ≤ y < 11 ≤ x` are handled by monotonicity of `Zrcp` plus the lower bound
`log log x − C₀ ≤ Zrcp x` (so that `exp (Zrcp x) ≥ log x · exp (−C₀)`).  The constant `C` may
depend on `C₀`; the caller instantiates `C₀` with the absolute constant of
`Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound`. -/
theorem casdiv_zrcp_ratio (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hMertens : ∀ t : ℝ, 11 ≤ t → |Work.BMF.Zrcp t - Real.log (Real.log t)| ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, 2 ≤ y → y ≤ x →
      Real.exp (Work.BMF.Zrcp y) ≤ C * Real.exp (Work.BMF.Zrcp x)
        * (Real.log y / Real.log x) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog11pos : 0 < Real.log 11 := Real.log_pos (by norm_num)
  -- the constant: the sum of the three constants forced by the three cases
  set C : ℝ := Real.exp (2 * C₀) + Real.exp (Work.BMF.Zrcp 11 + C₀) / Real.log 2
      + Real.log 11 / Real.log 2 with hCdef
  have hXpos : 0 < Real.exp (Work.BMF.Zrcp 11 + C₀) / Real.log 2 :=
    div_pos (Real.exp_pos _) hlog2pos
  have hYpos : 0 < Real.log 11 / Real.log 2 := div_pos hlog11pos hlog2pos
  have hCpos : 0 < C := by rw [hCdef]; linarith [Real.exp_pos (2 * C₀), hXpos, hYpos]
  have hC1 : Real.exp (2 * C₀) ≤ C := by rw [hCdef]; linarith [hXpos, hYpos]
  have hC2 : Real.exp (Work.BMF.Zrcp 11 + C₀) / Real.log 2 ≤ C := by
    rw [hCdef]; linarith [Real.exp_pos (2 * C₀), hYpos]
  have hC3 : Real.log 11 / Real.log 2 ≤ C := by
    rw [hCdef]; linarith [Real.exp_pos (2 * C₀), hXpos]
  refine ⟨C, hCpos, ?_⟩
  intro x y hy2 hyx
  have hlogypos : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hratiopos : 0 < Real.log y / Real.log x := div_pos hlogypos hlogxpos
  have hlogxne : Real.log x ≠ 0 := ne_of_gt hlogxpos
  by_cases hy11 : 11 ≤ y
  · -- Case `y ≥ 11`: the two-sided Mertens input gives `exp (Zrcp y) ≤ e^{C₀} log y` and
    -- `exp (Zrcp x) ≥ log x · e^{-C₀}`; the mismatch is absorbed by `C ≥ e^{2C₀}`.
    have hx11 : 11 ≤ x := le_trans hy11 hyx
    have hupy : Real.exp (Work.BMF.Zrcp y) ≤ Real.exp C₀ * Real.log y :=
      exp_Zrcp_le_mul_log C₀ hMertens hy11
    have hlox : Real.log x * Real.exp (-C₀) ≤ Real.exp (Work.BMF.Zrcp x) :=
      mul_exp_neg_le_exp_Zrcp C₀ hMertens hx11
    have hexpC : Real.exp (2 * C₀) * Real.exp (-C₀) = Real.exp C₀ := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (Work.BMF.Zrcp y) ≤ Real.exp C₀ * Real.log y := hupy
      _ = Real.exp C₀ * (Real.log y / Real.log x * Real.log x) := by
            rw [div_mul_cancel₀ _ hlogxne]
      _ = Real.exp (2 * C₀) * (Real.log y / Real.log x) * (Real.log x * Real.exp (-C₀)) := by
            rw [← hexpC]; ring
      _ ≤ Real.exp (2 * C₀) * (Real.log y / Real.log x) * Real.exp (Work.BMF.Zrcp x) :=
            mul_le_mul_of_nonneg_left hlox (mul_nonneg (Real.exp_pos _).le hratiopos.le)
      _ ≤ C * (Real.log y / Real.log x) * Real.exp (Work.BMF.Zrcp x) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hratiopos.le)
              (Real.exp_pos _).le
      _ = C * Real.exp (Work.BMF.Zrcp x) * (Real.log y / Real.log x) := by ring
  · push_neg at hy11
    by_cases hx11 : 11 ≤ x
    · -- Case `2 ≤ y < 11 ≤ x`: monotonicity of `Zrcp` gives `exp (Zrcp y) ≤ exp (Zrcp 11)`, and
      -- `C ≥ e^{Zrcp 11 + C₀}/log 2`, `log y ≥ log 2` finish, since `log x · e^{-C₀} ≤ exp (Zrcp x)`.
      have hZmono : Real.exp (Work.BMF.Zrcp y) ≤ Real.exp (Work.BMF.Zrcp 11) :=
        Real.exp_le_exp.mpr (Work.BMF.Zrcp_mono (le_of_lt hy11))
      have hlox : Real.log x * Real.exp (-C₀) ≤ Real.exp (Work.BMF.Zrcp x) :=
        mul_exp_neg_le_exp_Zrcp C₀ hMertens hx11
      have hlogy2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy2
      have hexpC' : Real.exp (Work.BMF.Zrcp 11 + C₀) * Real.exp (-C₀)
          = Real.exp (Work.BMF.Zrcp 11) := by
        rw [← Real.exp_add]; congr 1; ring
      have hmain1 : Real.exp (Work.BMF.Zrcp 11) ≤ C * Real.exp (-C₀) * Real.log y := by
        have hstep : Real.exp (Work.BMF.Zrcp 11 + C₀) ≤ C * Real.log y := by
          calc Real.exp (Work.BMF.Zrcp 11 + C₀)
              = Real.exp (Work.BMF.Zrcp 11 + C₀) / Real.log 2 * Real.log 2 := by
                  rw [div_mul_cancel₀ _ (ne_of_gt hlog2pos)]
            _ ≤ C * Real.log 2 := mul_le_mul_of_nonneg_right hC2 hlog2pos.le
            _ ≤ C * Real.log y := mul_le_mul_of_nonneg_left hlogy2 hCpos.le
        calc Real.exp (Work.BMF.Zrcp 11)
            = Real.exp (Work.BMF.Zrcp 11 + C₀) * Real.exp (-C₀) := hexpC'.symm
          _ ≤ (C * Real.log y) * Real.exp (-C₀) :=
                mul_le_mul_of_nonneg_right hstep (Real.exp_pos _).le
          _ = C * Real.exp (-C₀) * Real.log y := by ring
      calc Real.exp (Work.BMF.Zrcp y) ≤ Real.exp (Work.BMF.Zrcp 11) := hZmono
        _ ≤ C * Real.exp (-C₀) * Real.log y := hmain1
        _ = C * (Real.log x * Real.exp (-C₀)) * (Real.log y / Real.log x) := by field_simp
        _ ≤ C * Real.exp (Work.BMF.Zrcp x) * (Real.log y / Real.log x) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlox hCpos.le)
                hratiopos.le
    · -- Case `x < 11`: monotonicity `Zrcp y ≤ Zrcp x` plus the ratio bound
      -- `log y / log x ≥ log 2 / log 11 ≥ 1/C`.
      push_neg at hx11
      have hZmono : Real.exp (Work.BMF.Zrcp y) ≤ Real.exp (Work.BMF.Zrcp x) :=
        Real.exp_le_exp.mpr (Work.BMF.Zrcp_mono hyx)
      have hlogy2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy2
      have hlogx11 : Real.log x ≤ Real.log 11 :=
        Real.log_le_log (by linarith) (le_of_lt hx11)
      have hratio_ge : Real.log 2 / Real.log 11 ≤ Real.log y / Real.log x := by
        have ha : Real.log 2 / Real.log 11 ≤ Real.log 2 / Real.log x :=
          div_le_div_of_nonneg_left hlog2pos.le hlogxpos hlogx11
        have hb : Real.log 2 / Real.log x ≤ Real.log y / Real.log x :=
          div_le_div_of_nonneg_right hlogy2 hlogxpos.le
        linarith
      have hCratio : 1 ≤ C * (Real.log y / Real.log x) := by
        have h := mul_le_mul hC3 hratio_ge (le_of_lt (div_pos hlog2pos hlog11pos)) hCpos.le
        have h1 : Real.log 11 / Real.log 2 * (Real.log 2 / Real.log 11) = 1 := by field_simp
        linarith [h, h1.le, h1.ge]
      calc Real.exp (Work.BMF.Zrcp y) ≤ Real.exp (Work.BMF.Zrcp x) := hZmono
        _ = Real.exp (Work.BMF.Zrcp x) * 1 := by ring
        _ ≤ Real.exp (Work.BMF.Zrcp x) * (C * (Real.log y / Real.log x)) :=
              mul_le_mul_of_nonneg_left hCratio (Real.exp_pos _).le
        _ = C * Real.exp (Work.BMF.Zrcp x) * (Real.log y / Real.log x) := by ring

end Work.BMF.mrlas
