import Mathlib
import Submission.Work.GM.Energy.Defs
import Submission.Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay

/-!
# The flat-top bump used for GM Lemma 11.7

GM's Lemma 11.7 needs a fixed smooth bump `ψ` which equals `1` on `[0,1]`, together with the
rapid decay of its Fourier transform.  We take the Guth–Maynard bump `bumpW` (`= 1` on
`[6/5, 9/5]`, supported in `[1,2]`) and rescale:

`ψ x = w (6/5 + 3x/5)`, so that `ψ = 1` on `[0,1]` and `ψ` is supported in `[-1/3, 4/3]`.

Everything about `ψ` that the proof of `Rfun_local` needs is collected here: smoothness,
compact support, the value on `[0,1]`, the Fourier decay `‖𝓕 ψ‖ ≤ C_j |ξ|^{-j}`, the trivial
bound `‖𝓕 ψ‖ ≤ ∫ ‖ψ‖`, integrability of `𝓕 ψ`, and the Fourier inversion formula
`ψ s = ∫ ξ, 𝐞 (ξ s) · 𝓕ψ ξ`.
-/

namespace Work.GM.Energy.RLocal

open Complex Finset MeasureTheory
open scoped BigOperators FourierTransform

set_option autoImplicit false

/-- The flat-top bump `ψ x = w(6/5 + 3x/5)`: smooth, compactly supported, and `= 1` on `[0,1]`. -/
noncomputable def psiBump (x : ℝ) : ℝ := Submission.LargeValues.bumpW (6 / 5 + 3 / 5 * x)

/-- The complexified bump, to which the Fourier transform is applied. -/
noncomputable def PsiBump (x : ℝ) : ℂ := (psiBump x : ℂ)

lemma psiBump_eq_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : psiBump x = 1 := by
  unfold psiBump
  apply Submission.LargeValues.bumpW_eq_one
  constructor <;> linarith [hx.1, hx.2]

lemma psiBump_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psiBump := by
  unfold psiBump
  exact Submission.LargeValues.bumpW_contDiff.comp (by fun_prop)

lemma psiBump_continuous : Continuous psiBump := psiBump_contDiff.continuous

lemma psiBump_support_subset : Function.support psiBump ⊆ Set.Icc (-(1 / 3) : ℝ) (4 / 3) := by
  intro x hx
  rw [Function.mem_support] at hx
  have hmem : 6 / 5 + 3 / 5 * x ∈ Set.Icc (1 : ℝ) 2 := by
    by_contra hc
    exact hx (Submission.LargeValues.bumpW_eq_zero_of_notMem hc)
  constructor <;> linarith [hmem.1, hmem.2]

lemma psiBump_hasCompactSupport : HasCompactSupport psiBump :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc psiBump_support_subset

lemma PsiBump_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) PsiBump :=
  Complex.ofRealCLM.contDiff.comp psiBump_contDiff

lemma PsiBump_continuous : Continuous PsiBump :=
  Complex.continuous_ofReal.comp psiBump_continuous

lemma PsiBump_hasCompactSupport : HasCompactSupport PsiBump :=
  psiBump_hasCompactSupport.comp_left (by simp)

lemma PsiBump_integrable : Integrable PsiBump :=
  PsiBump_continuous.integrable_of_hasCompactSupport PsiBump_hasCompactSupport

/-- Fourier decay of the bump: for every `j` there is `C ≥ 0` with `‖𝓕 ψ ξ‖ ≤ C / |ξ| ^ j`. -/
theorem PsiBump_fourier_decay (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, ξ ≠ 0 → ‖𝓕 PsiBump ξ‖ ≤ C / |ξ| ^ j :=
  Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay j PsiBump_contDiff
    PsiBump_hasCompactSupport

/-- The trivial bound `‖𝓕 ψ ξ‖ ≤ ∫ ‖ψ‖`. -/
lemma PsiBump_fourier_le_integral (ξ : ℝ) : ‖𝓕 PsiBump ξ‖ ≤ ∫ x, ‖PsiBump x‖ := by
  rw [Real.fourier_eq]
  calc ‖∫ v, Real.fourierChar (-inner ℝ v ξ) • PsiBump v‖
      ≤ ∫ v, ‖Real.fourierChar (-inner ℝ v ξ) • PsiBump v‖ := norm_integral_le_integral_norm _
    _ = ∫ v, ‖PsiBump v‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        simp only [Circle.norm_smul]

lemma continuous_fourier_PsiBump : Continuous (𝓕 PsiBump) := by
  rw [show (𝓕 PsiBump) = VectorFourier.fourierIntegral Real.fourierChar (volume : Measure ℝ)
      (innerₗ ℝ) PsiBump from rfl]
  exact VectorFourier.fourierIntegral_continuous (μ := (volume : Measure ℝ)) (L := innerₗ ℝ)
    Real.continuous_fourierChar (by fun_prop) PsiBump_integrable

lemma PsiBump_fourier_integrable : Integrable (𝓕 PsiBump) := by
  obtain ⟨C, hC0, hC⟩ := PsiBump_fourier_decay 2
  set M : ℝ := ∫ x, ‖PsiBump x‖ with hM
  have hM0 : 0 ≤ M := integral_nonneg fun x => norm_nonneg _
  have hMC : (0 : ℝ) ≤ M + C := by linarith
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (2 * (M + C)))
    continuous_fourier_PsiBump.aestronglyMeasurable ?_
  filter_upwards with ξ
  have hpos : (0 : ℝ) < 1 + ξ ^ 2 := by positivity
  rcases le_or_gt |ξ| 1 with h | h
  · have hsq : ξ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ξ]
    have hhalf : (1 : ℝ) ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
      rw [show (2 : ℝ) * (1 + ξ ^ 2)⁻¹ = 2 / (1 + ξ ^ 2) by rw [div_eq_mul_inv],
        le_div_iff₀ hpos]
      linarith
    calc ‖𝓕 PsiBump ξ‖ ≤ M := PsiBump_fourier_le_integral ξ
      _ ≤ M + C := by linarith [hC0]
      _ ≤ (2 * (M + C)) * (1 + ξ ^ 2)⁻¹ := by
          calc M + C = (M + C) * 1 := (mul_one _).symm
            _ ≤ (M + C) * (2 * (1 + ξ ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hhalf hMC
            _ = (2 * (M + C)) * (1 + ξ ^ 2)⁻¹ := by ring
  · have hξne : ξ ≠ 0 := by intro h0; rw [h0, abs_zero] at h; norm_num at h
    have hsq : 1 ≤ ξ ^ 2 := by rw [← sq_abs]; nlinarith [abs_pos.mpr hξne]
    have hd := hC ξ hξne
    have h3 : ((|ξ| : ℝ) ^ 2)⁻¹ ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
      have hge : (1 : ℝ) ≤ (|ξ|) ^ 2 := by nlinarith [abs_nonneg ξ]
      have hgt : (0 : ℝ) < (|ξ|) ^ 2 := lt_of_lt_of_le one_pos hge
      have hthis : (2 : ℝ) * (1 + ξ ^ 2)⁻¹ = ((1 + ξ ^ 2) / 2)⁻¹ := by rw [inv_div]; ring
      rw [hthis, inv_le_inv₀ hgt (by positivity)]
      linarith [sq_abs ξ, hge]
    calc ‖𝓕 PsiBump ξ‖ ≤ C / |ξ| ^ 2 := hd
      _ = C * ((|ξ| : ℝ) ^ 2)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ C * (2 * (1 + ξ ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h3 hC0
      _ ≤ (M + C) * (2 * (1 + ξ ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (2 * (M + C)) * (1 + ξ ^ 2)⁻¹ := by ring

/-- **Fourier inversion for the bump.** -/
theorem PsiBump_fourier_inversion (s : ℝ) :
    PsiBump s = ∫ ξ, Real.fourierChar (inner ℝ ξ s) • (𝓕 PsiBump) ξ := by
  have hinv := Continuous.fourierInv_fourier_eq (f := PsiBump) PsiBump_continuous PsiBump_integrable
    PsiBump_fourier_integrable
  rw [← congrFun hinv s, Real.fourierInv_eq]

end Work.GM.Energy.RLocal
