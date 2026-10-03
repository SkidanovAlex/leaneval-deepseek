import Mathlib
import Submission.Work.KMTAreas.SupNorm.WavePacket
import Submission.Work.KMTAreas.SupNorm.eLpNorm_comp_mul_left_eq
import Submission.Work.KMTAreas.SupNorm.Norms
import Submission.Port.Aesm

/-!
# The `L^p` norm of the wave packet

For `δ > 0` and `x₀ : ℝ` the *wave packet* of the `SupNorm` area is

`f_δ(x) = δ · e(x₀ x) · 𝓕⁻η(δ x)`,   `η = kmtEta`,

i.e. the inverse Fourier transform of the frequency bump `ξ ↦ η((ξ - x₀)/δ)` concentrated at
scale `δ` around `x₀` (`Work.KMTAreas.SupNorm.wavePacket_apply`).

This module computes its `ℒᵖ` seminorm.  Since the modulus of the modulation `e(x₀ x)` is `1`, the
`ℒᵖ` seminorm of `f_δ` is that of the dilation `x ↦ δ · 𝓕⁻η(δ x)`, and the two scaling factors
combine into `δ^{1-1/p}`:

`‖f_δ‖_p = δ^{1-1/p} ‖𝓕⁻η‖_p`   (`1 ≤ p < ∞`).

The auxiliary fact that `‖𝓕⁻η‖_p` is a *positive real* (i.e. `𝓕⁻η` is a non-zero Schwartz function)
is proved alongside: `𝓕⁻η` is continuous (it is a Schwartz function), and if it vanished almost
everywhere it would vanish identically, hence so would `η = 𝓕(𝓕⁻η)`, contradicting `η 0 = 1`.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace Work.KMTAreas.SupNorm

open Work.KMTAreas.A7 (etaMult_psiSch etaMult_psiSch_coe etaMult_kmtEtaSch
  etaMult_kmtEtaSch_coe)

/-- The inverse Fourier transform `𝓕⁻η` of the cutoff `η = kmtEta` is (the coercion of) a
Schwartz function, hence continuous and in every `L^p`. -/
lemma kmtPsi_continuous : Continuous (FourierTransformInv.fourierInv Work.KMTContract.kmtEta) := by
  rw [← etaMult_psiSch_coe]
  exact etaMult_psiSch.continuous

lemma kmtPsi_memLp (p : ENNReal) :
    MeasureTheory.MemLp (FourierTransformInv.fourierInv Work.KMTContract.kmtEta) p MeasureTheory.volume := by
  rw [← etaMult_psiSch_coe]
  exact SchwartzMap.memLp etaMult_psiSch p MeasureTheory.volume

/-- `𝓕⁻η` does not vanish (as a function). -/
lemma kmtPsi_ne_zero : FourierTransformInv.fourierInv Work.KMTContract.kmtEta ≠ 0 := by
  intro h0
  -- `𝓕⁻η = 0` forces `η = 𝓕 (𝓕⁻η) = 𝓕 0 = 0`, contradicting `η 0 = 1`.
  have hpsi0 : etaMult_psiSch = 0 := by
    have h' : (⇑etaMult_psiSch : ℝ → ℂ) = 0 := by
      rw [etaMult_psiSch_coe]; exact h0
    ext x
    exact congrFun h' x
  have hkmt0 : etaMult_kmtEtaSch = 0 := by
    have h := FourierInvPair.fourier_fourierInv_eq (E := SchwartzMap ℝ ℂ) (F := SchwartzMap ℝ ℂ)
      etaMult_kmtEtaSch
    rw [show FourierTransformInv.fourierInv etaMult_kmtEtaSch = etaMult_psiSch from rfl,
      hpsi0] at h
    simpa using h.symm
  have h1 : etaMult_kmtEtaSch 0 = 1 := by
    rw [etaMult_kmtEtaSch_coe]
    exact Work.KMTContract.kmtEta_one (by norm_num)
  rw [hkmt0] at h1
  simp at h1

lemma kmtPsi_eLpNorm_ne_zero {p : ENNReal} (hp1 : 1 ≤ p) :
    MeasureTheory.eLpNorm (FourierTransformInv.fourierInv Work.KMTContract.kmtEta) p MeasureTheory.volume ≠ 0 := by
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hp1; simp at hp1
  intro h0
  have hae := (MeasureTheory.eLpNorm_eq_zero_iff hp0).mp h0
  exact kmtPsi_ne_zero
    ((Continuous.ae_eq_iff_eq MeasureTheory.volume kmtPsi_continuous continuous_zero).mp hae)

theorem eLpNorm_wavePacket_and_kernel {p : ENNReal} (hp1 : 1 ≤ p) (hp2 : p < ⊤) :
    (∃ c₀ : ℝ, 0 < c₀ ∧ MeasureTheory.eLpNorm (FourierTransformInv.fourierInv Work.KMTContract.kmtEta) p MeasureTheory.volume = ENNReal.ofReal c₀)
    ∧ (∀ {x₀ δ : ℝ} (hδ : 0 < δ),
        MeasureTheory.eLpNorm (⇑(Work.KMTAreas.SupNorm.wavePacket x₀ δ hδ)) p MeasureTheory.volume
          = ENNReal.ofReal (δ ^ (1 - 1 / p.toReal))
              * MeasureTheory.eLpNorm (FourierTransformInv.fourierInv Work.KMTContract.kmtEta) p MeasureTheory.volume) := by
  have hpT : p ≠ ⊤ := ne_of_lt hp2
  have htop : MeasureTheory.eLpNorm (FourierTransformInv.fourierInv Work.KMTContract.kmtEta) p MeasureTheory.volume ≠ ⊤ :=
    ne_of_lt (kmtPsi_memLp p).eLpNorm_lt_top
  refine ⟨⟨(MeasureTheory.eLpNorm (FourierTransformInv.fourierInv Work.KMTContract.kmtEta) p MeasureTheory.volume).toReal,
      ENNReal.toReal_pos (kmtPsi_eLpNorm_ne_zero hp1) htop, (ENNReal.ofReal_toReal htop).symm⟩, ?_⟩
  intro x₀ δ hδ
  -- The modulation has modulus one, so only `δ · 𝓕⁻η(δ x)` matters for the seminorm.
  have hchar : ∀ t : ℝ, ‖(Real.fourierChar t : ℂ)‖ₑ = 1 := by
    intro t
    rw [enorm_eq_nnnorm, ENNReal.coe_eq_one]
    exact Subtype.ext (Circle.norm_coe _)
  have hstep : MeasureTheory.eLpNorm (⇑(wavePacket x₀ δ hδ)) p MeasureTheory.volume
      = MeasureTheory.eLpNorm (fun x : ℝ => (δ : ℂ) * FourierTransformInv.fourierInv Work.KMTContract.kmtEta (δ * x)) p MeasureTheory.volume := by
    apply MeasureTheory.eLpNorm_congr_enorm_ae
      (hf := (wavePacket x₀ δ hδ).continuous.aestronglyMeasurable)
      (hg := (continuous_const.mul (kmtPsi_continuous.comp
        (continuous_const.mul continuous_id))).aestronglyMeasurable)
    filter_upwards with x
    rw [wavePacket_apply hδ x]
    simp only [enorm_mul, hchar (x₀ * x), mul_one, Pi.mul_apply, Function.comp_apply, id]
  -- Pull the constant `δ` out of the seminorm.
  have hstep2 : MeasureTheory.eLpNorm (fun x : ℝ => (δ : ℂ) * FourierTransformInv.fourierInv Work.KMTContract.kmtEta (δ * x)) p MeasureTheory.volume
      = ‖(δ : ℂ)‖ₑ * MeasureTheory.eLpNorm (fun x : ℝ => FourierTransformInv.fourierInv Work.KMTContract.kmtEta (δ * x)) p MeasureTheory.volume := by
    rw [show (fun x : ℝ => (δ : ℂ) * FourierTransformInv.fourierInv Work.KMTContract.kmtEta (δ * x))
        = (δ : ℂ) • (fun x : ℝ => FourierTransformInv.fourierInv Work.KMTContract.kmtEta (δ * x)) from rfl]
    rw [MeasureTheory.eLpNorm_const_smul]
  -- The dilation `x ↦ δ x` contributes the Jacobian factor `(δ⁻¹)^{1/p}`.
  have hstep3 : MeasureTheory.eLpNorm (fun x : ℝ => FourierTransformInv.fourierInv Work.KMTContract.kmtEta (δ * x)) p MeasureTheory.volume
      = ENNReal.ofReal δ⁻¹ ^ ((1 / p : ENNReal).toReal) * MeasureTheory.eLpNorm (FourierTransformInv.fourierInv Work.KMTContract.kmtEta) p MeasureTheory.volume :=
    eLpNorm_comp_mul_left_eq _ hδ hpT kmtPsi_continuous.aestronglyMeasurable
  have hdelta : ‖(δ : ℂ)‖ₑ = ENNReal.ofReal δ := by
    rw [enorm_eq_nnnorm, Complex.nnnorm_real, ← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [Real.norm_eq_abs, abs_of_pos hδ]
  have hpow : ENNReal.ofReal δ⁻¹ ^ ((1 / p : ENNReal).toReal) = ENNReal.ofReal (δ ^ (-(1 / p.toReal))) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hδ.le) (by positivity)]
    congr 1
    rw [Real.rpow_neg hδ.le, Real.inv_rpow hδ.le]
  -- `δ · δ^{-1/p} = δ^{1 - 1/p}`.
  have hmain : ENNReal.ofReal δ * ENNReal.ofReal δ⁻¹ ^ ((1 / p : ENNReal).toReal)
      = ENNReal.ofReal (δ ^ (1 - 1 / p.toReal)) := by
    rw [hpow, ← ENNReal.ofReal_mul hδ.le]
    have h := Real.rpow_add hδ (1 : ℝ) (-(1 / p.toReal))
    rw [Real.rpow_one] at h
    rw [← h]
    rw [show (1 : ℝ) + -(1 / p.toReal) = 1 - 1 / p.toReal from by ring]
  rw [hstep, hstep2, hstep3, hdelta, ← mul_assoc, hmain]

end Work.KMTAreas.SupNorm
