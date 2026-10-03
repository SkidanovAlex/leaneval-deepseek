import Mathlib
import Submission.Work.Fatou.DevH.deriv_setup
import Submission.Work.Fatou.DevH.basic
import Submission.Work.Fatou.Smooth
import Submission.Work.Fatou.Setup

namespace Work.Fatou.DevH

open MandelDim

/-- The explicit action of the correction term `D devH - id`: the sum of the
`χ(Re ζ)·(F'(w)-1)`-part (identity direction) and the `ε(w)·χ'(Re ζ)`-part (`Re` direction),
where `w = x₀ + ζ - 1`. -/
theorem devHCorr_apply' (x₀ : ℝ) (F : ℂ → ℂ) (ζ v : ℂ) :
    devHCorr x₀ F ζ v =
      ((smoothstep ζ.re : ℝ) : ℂ) * (deriv F (shiftArg x₀ ζ) - 1) * v
        + eps F (shiftArg x₀ ζ) * ((v.re : ℂ) * ((deriv smoothstep ζ.re : ℝ) : ℂ)) := by
  simp only [devHCorr, add_apply, smul_apply,
    mulCLM_apply, chiDerivCLM_apply, smul_eq_mul]
  ring

/-- The two coefficients in `D devH = id + c2·id + c1·(Re ·)` are small: `‖c1‖ ≤ 1/16` and
`‖c2‖ ≤ 1/32`, hence also the operator norm of the correction term is `≤ 3/32`.
(`c1 = ε(x₀+ζ-1)·χ'(Re ζ)`, `c2 = χ(Re ζ)·(F'(x₀+ζ-1) - 1)`; see
`Submission/Work/Fatou/DevH/deriv_setup.lean`.) -/
theorem devHCorr_bounds {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂)) (ζ : ℂ) :
    ‖Work.Fatou.DevH.devHCorr (Work.Fatou.xOf b₁ b₂) F ζ‖ ≤ 3 / 32 ∧
    ‖Work.Fatou.DevH.c1 (Work.Fatou.xOf b₁ b₂) F ζ‖ ≤ 1 / 16 ∧
    ‖Work.Fatou.DevH.c2 (Work.Fatou.xOf b₁ b₂) F ζ‖ ≤ 1 / 32 := by
  by_cases hin : ζ.re ≤ 1 / 8 ∨ 15 / 8 ≤ ζ.re
  · -- the cut-off and its derivative both vanish: the correction term is `0`
    have hχ : smoothstep ζ.re = 0 := by
      rcases hin with h | h
      · exact smoothstep_eq_zero_of_le h
      · exact smoothstep_eq_zero_of_ge h
    have hχ' : deriv smoothstep ζ.re = 0 := by
      rcases hin with h | h
      · exact deriv_smoothstep_eq_zero_of_le h
      · exact deriv_smoothstep_eq_zero_of_ge h
    have hc1 : c1 (xOf b₁ b₂) F ζ = 0 := by simp [c1, hχ']
    have hc2 : c2 (xOf b₁ b₂) F ζ = 0 := by simp [c2, hχ]
    have hcorr : devHCorr (xOf b₁ b₂) F ζ = 0 := by
      ext v
      rw [devHCorr_apply']
      simp [hχ, hχ']
    refine ⟨?_, ?_, ?_⟩
    · rw [hcorr, norm_zero]; norm_num
    · rw [hc1, norm_zero]; norm_num
    · rw [hc2, norm_zero]; norm_num
  · -- the transition strip: `w = x₀ + ζ - 1 ∈ Qreg`, so `ε` and `F' - 1` are small
    push Not at hin
    obtain ⟨h1, h2⟩ := hin
    have hle1 : (1 / 8 : ℝ) ≤ ζ.re := le_of_lt h1
    have hle2 : ζ.re ≤ 15 / 8 := le_of_lt h2
    have hw : shiftArg (xOf b₁ b₂) ζ ∈ Qreg b₁ b₂ := shiftArg_mem_Qreg hadm hle1 hle2
    have heps : ‖eps F (shiftArg (xOf b₁ b₂) ζ)‖ ≤ 1 / 32 := (hF.2 _ hw).1
    have hder : ‖deriv F (shiftArg (xOf b₁ b₂) ζ) - 1‖ ≤ 1 / 32 := (hF.2 _ hw).2
    have hChi : |smoothstep ζ.re| ≤ 1 :=
      abs_le.mpr ⟨by linarith [(smoothstep_mem_Icc ζ.re).1], (smoothstep_mem_Icc ζ.re).2⟩
    have hChi' : |deriv smoothstep ζ.re| ≤ 2 := abs_deriv_smoothstep_le ζ.re
    refine ⟨?_, ?_, ?_⟩
    · -- operator norm of the correction term
      refine ContinuousLinearMap.opNorm_le_bound (devHCorr (xOf b₁ b₂) F ζ)
        (M := 3 / 32) (by norm_num) (fun v => ?_)
      rw [devHCorr_apply']
      have hA : ‖((smoothstep ζ.re : ℝ) : ℂ) * (deriv F (shiftArg (xOf b₁ b₂) ζ) - 1) * v‖
          ≤ 1 / 32 * ‖v‖ := by
        rw [norm_mul, norm_mul, Work.Fatou.norm_ofReal_cast]
        calc |smoothstep ζ.re| * ‖deriv F (shiftArg (xOf b₁ b₂) ζ) - 1‖ * ‖v‖
            ≤ 1 * (1 / 32) * ‖v‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              exact mul_le_mul hChi hder (norm_nonneg _) (by norm_num)
          _ = 1 / 32 * ‖v‖ := by ring
      have hB : ‖eps F (shiftArg (xOf b₁ b₂) ζ) *
            (((v.re : ℝ) : ℂ) * ((deriv smoothstep ζ.re : ℝ) : ℂ))‖ ≤ 2 / 32 * ‖v‖ := by
        rw [norm_mul, norm_mul, Work.Fatou.norm_ofReal_cast, Work.Fatou.norm_ofReal_cast]
        calc ‖eps F (shiftArg (xOf b₁ b₂) ζ)‖ * (|v.re| * |deriv smoothstep ζ.re|)
            ≤ (1 / 32) * (‖v‖ * 2) := by
              apply mul_le_mul heps _ (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
              exact mul_le_mul (Complex.abs_re_le_norm v) hChi' (abs_nonneg _) (norm_nonneg _)
          _ = 2 / 32 * ‖v‖ := by ring
      have h := norm_add_le
        (((smoothstep ζ.re : ℝ) : ℂ) * (deriv F (shiftArg (xOf b₁ b₂) ζ) - 1) * v)
        (eps F (shiftArg (xOf b₁ b₂) ζ) * (((v.re : ℝ) : ℂ) * ((deriv smoothstep ζ.re : ℝ) : ℂ)))
      linarith
    · -- `‖c1‖ ≤ 1/16`
      rw [show c1 (xOf b₁ b₂) F ζ = eps F (shiftArg (xOf b₁ b₂) ζ) *
            ((deriv smoothstep ζ.re : ℝ) : ℂ) from rfl]
      rw [norm_mul, Work.Fatou.norm_ofReal_cast]
      calc ‖eps F (shiftArg (xOf b₁ b₂) ζ)‖ * |deriv smoothstep ζ.re|
          ≤ (1 / 32) * 2 := mul_le_mul heps hChi' (abs_nonneg _) (by norm_num)
        _ = 1 / 16 := by norm_num
    · -- `‖c2‖ ≤ 1/32`
      rw [show c2 (xOf b₁ b₂) F ζ = ((smoothstep ζ.re : ℝ) : ℂ) *
            (deriv F (shiftArg (xOf b₁ b₂) ζ) - 1) from rfl]
      rw [norm_mul, Work.Fatou.norm_ofReal_cast]
      calc |smoothstep ζ.re| * ‖deriv F (shiftArg (xOf b₁ b₂) ζ) - 1‖
          ≤ 1 * (1 / 32) := mul_le_mul hChi hder (norm_nonneg _) (by norm_num)
        _ = 1 / 32 := by norm_num

end Work.Fatou.DevH
