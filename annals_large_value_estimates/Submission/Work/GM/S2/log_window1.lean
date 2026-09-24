import Mathlib
import Submission.Work.GM.S2.Defs
import Submission.Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay

/-!
# Guth–Maynard §6: the log-window representation for `ψ(u)/u`

This is the companion of `Work.GM.S2.log_window`.  We put `ψ(u) = w(u)²` and
`g₁(s) = e^s ψ(e^s)`, so that `ψ(u) = g₁(log u)/u` for `u > 0`.  Writing `ĝ₁` for the
Fourier transform of `g₁`, Fourier inversion for `g₁` gives the representation

`ψ(u) = (1/u) ∫ ĝ₁(ξ) u^{2πiξ} dξ`  (`u > 0`),

together with the quantitative facts about `ĝ₁` needed to justify it (integrability, decay
`≪ (1+|ξ|)^{-2}`, finiteness of `∫ ‖ĝ₁‖`).
-/

open MeasureTheory
open scoped FourierTransform

namespace Work.GM.S2

/-- `s ↦ e^s ψ(e^s)` is `C^∞`. -/
lemma logWindow1_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) logWindow1 := by
  unfold logWindow1
  exact Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.mul ((Submission.LargeValues.bumpW_contDiff.pow 2).comp Real.contDiff_exp))

/-- `s ↦ e^s ψ(e^s)` is supported in `[0, log 2]`, hence compactly supported. -/
lemma logWindow1_hasCompactSupport : HasCompactSupport logWindow1 := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro s hs
  have hs' : psi (Real.exp s) ≠ 0 := by
    intro h
    apply hs
    simp [logWindow1, h]
  have hb : Submission.LargeValues.bumpW (Real.exp s) ≠ 0 := by
    intro h
    apply hs'
    simp [psi, h]
  have hmem : Real.exp s ∈ Set.Icc (1 : ℝ) 2 := by
    by_contra h
    exact hb (Submission.LargeValues.bumpW_eq_zero_of_notMem h)
  obtain ⟨h1, h2⟩ := hmem
  refine ⟨?_, ?_⟩
  · have h := Real.log_le_log (show (0 : ℝ) < 1 by norm_num) h1
    rwa [Real.log_one, Real.log_exp] at h
  · have h2' : Real.exp s ≤ Real.exp (Real.log 2) := by
      rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mp h2'

lemma logWindow1_integrable : Integrable logWindow1 :=
  logWindow1_contDiff.continuous.integrable_of_hasCompactSupport logWindow1_hasCompactSupport

/-- The Fourier transform of an `L¹` function is continuous. -/
lemma ghat1_continuous : Continuous ghat1 := by
  unfold ghat1
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ logWindow1_integrable

/-- `‖ĝ₁(ξ)‖ ≤ ∫ ‖g₁‖` for every `ξ`. -/
lemma norm_ghat1_le_integral : ∀ ξ : ℝ, ‖ghat1 ξ‖ ≤ ∫ s, ‖logWindow1 s‖ := by
  intro ξ
  simp only [ghat1]
  rw [Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp [Circle.norm_smul]

/-- Decay of `ĝ₁`: `‖ĝ₁(ξ)‖ ≤ C (1 + |ξ|)^{-2}`. -/
lemma ghat1_decay_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, ‖ghat1 ξ‖ ≤ C / (1 + |ξ|) ^ 2 := by
  obtain ⟨C₀, hC₀, hb⟩ :=
    Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay 2
      logWindow1_contDiff logWindow1_hasCompactSupport
  set B : ℝ := ∫ s, ‖logWindow1 s‖ with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact integral_nonneg (fun s => norm_nonneg _)
  have hB : ∀ ξ : ℝ, ‖ghat1 ξ‖ ≤ B := by
    intro ξ
    rw [hBdef]
    exact norm_ghat1_le_integral ξ
  refine ⟨4 * B + 4 * C₀ + 1, by linarith, fun ξ => ?_⟩
  have hden : 0 < (1 + |ξ|) ^ 2 := by positivity
  rw [le_div_iff₀ hden]
  by_cases h : |ξ| ≤ 1
  · have h4 : (1 + |ξ|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg ξ]
    have h4nn : 0 ≤ (1 + |ξ|) ^ 2 := by positivity
    calc ‖ghat1 ξ‖ * (1 + |ξ|) ^ 2 ≤ B * 4 :=
          mul_le_mul (hB ξ) h4 h4nn (le_trans (norm_nonneg _) (hB ξ))
      _ ≤ 4 * B + 4 * C₀ + 1 := by linarith
  · have h1 : 1 < |ξ| := not_le.mp h
    have hξ : ξ ≠ 0 := by rintro rfl; norm_num at h1
    have h2 : (1 + |ξ|) ^ 2 ≤ 4 * |ξ| ^ 2 := by nlinarith [abs_pos.mpr hξ]
    have h2nn : 0 ≤ (1 + |ξ|) ^ 2 := by positivity
    calc ‖ghat1 ξ‖ * (1 + |ξ|) ^ 2 ≤ (C₀ / |ξ| ^ 2) * (4 * |ξ| ^ 2) :=
          mul_le_mul (hb ξ hξ) h2 h2nn (le_trans (norm_nonneg _) (hb ξ hξ))
      _ = 4 * C₀ := by field_simp
      _ ≤ 4 * B + 4 * C₀ + 1 := by linarith

/-- `ĝ₁` is integrable (it decays like `(1+|ξ|)^{-2}`). -/
lemma ghat1_integrable : Integrable ghat1 := by
  obtain ⟨C, hC, hb⟩ := ghat1_decay_bound
  have hbase : Integrable (fun ξ : ℝ => (1 + ‖ξ‖) ^ (-2 : ℝ)) volume :=
    integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  refine (hbase.const_mul C).mono' ghat1_continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => ?_))
  have h1 : C / (1 + |ξ|) ^ 2 = C * (1 + ‖ξ‖) ^ (-2 : ℝ) := by
    rw [Real.norm_eq_abs, div_eq_mul_inv, ← Real.rpow_two]
    congr 1
    rw [← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |ξ|)]
  rw [← h1]
  exact hb ξ

/-- **Fourier inversion for the log-window `g₁`.**
`g₁(s) = ∫ ĝ₁(ξ) (e^s)^{2πiξ} dξ` for every `s`. -/
lemma ghat1_fourier_inversion (s : ℝ) :
    logWindow1 s = ∫ ξ, ghat1 ξ * ((Real.exp s : ℝ) : ℂ) ^ (2 * Real.pi * Complex.I * (ξ : ℂ)) := by
  have hinv : 𝓕⁻ (𝓕 logWindow1) = logWindow1 :=
    Continuous.fourierInv_fourier_eq logWindow1_contDiff.continuous logWindow1_integrable ghat1_integrable
  have h1 : 𝓕⁻ ghat1 = logWindow1 := by
    unfold ghat1
    exact hinv
  have key : 𝓕⁻ ghat1 s
      = ∫ ξ, ghat1 ξ * ((Real.exp s : ℝ) : ℂ) ^ (2 * Real.pi * Complex.I * (ξ : ℂ)) := by
    rw [Real.fourierInv_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    simp only []
    have hne : ((Real.exp s : ℝ) : ℂ) ≠ 0 := by
      simp
    have hlog : Complex.log ((Real.exp s : ℝ) : ℂ) = (s : ℂ) := by
      rw [← Complex.ofReal_log (Real.exp_pos s).le, Real.log_exp]
    have hexp : Complex.exp (((2 * Real.pi * (v * s) : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I * (v : ℂ))) := by
      congr 1
      push_cast
      ring
    rw [Real.inner_apply, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply, hexp,
      Complex.cpow_def_of_ne_zero hne, hlog]
    ring
  rwa [h1] at key

theorem log_window1 :
    (∀ u : ℝ, 0 < u →
      ((Work.GM.S2.psi u : ℝ) : ℂ) = (1 / (u : ℂ)) * MeasureTheory.integral MeasureTheory.volume
        (fun ξ : ℝ => Work.GM.S2.ghat1 ξ *
          (u : ℂ) ^ (2 * Real.pi * Complex.I * (ξ : ℂ)))) ∧
    MeasureTheory.Integrable Work.GM.S2.ghat1 ∧
    (∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, ‖Work.GM.S2.ghat1 ξ‖ ≤ C / (1 + |ξ|) ^ 2) ∧
    (∃ M : ℝ, 0 < M ∧ (∫ ξ, ‖Work.GM.S2.ghat1 ξ‖) ≤ M) := by
  refine ⟨?_, ghat1_integrable, ghat1_decay_bound, ?_⟩
  · intro u hu
    have h := ghat1_fourier_inversion (Real.log u)
    simp only [logWindow1, Real.exp_log hu] at h
    have hcast : ((u * psi u : ℝ) : ℂ) = (u : ℂ) * ((psi u : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast] at h
    have hne : (u : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu
    have step : (1 / (u : ℂ)) * ((u : ℂ) * ((psi u : ℝ) : ℂ)) = ((psi u : ℝ) : ℂ) := by
      rw [one_div, inv_mul_cancel_left₀ hne]
    rw [← step, h]
  · refine ⟨(∫ ξ, ‖ghat1 ξ‖) + 1, ?_, ?_⟩
    · have hnn : (0 : ℝ) ≤ ∫ ξ, ‖ghat1 ξ‖ :=
        integral_nonneg (f := fun ξ : ℝ => ‖ghat1 ξ‖) (fun ξ => norm_nonneg _)
      linarith
    · exact le_add_of_nonneg_right zero_le_one

end Work.GM.S2
