/-
The key `L²` estimate for the operator `Λ^s ∘ M_γ ∘ Λ^{-s}`, proved by Plancherel plus
Peetre's inequality and Young's inequality for convolutions.

`mms_Phi s γS k = Λ^s (γS · Λ^{-s} k)`, and on the Fourier side
`𝓕 (mms_Phi s γS k) ξ = ⟨ξ⟩^s · ∫ η, 𝓕γ(η) ⟨ξ-η⟩^{-s} 𝓕k(ξ-η) dη`.
Peetre's inequality gives `⟨ξ⟩^s ⟨ξ-η⟩^{-s} ≤ 2^{|s|/2} ⟨η⟩^{|s|}`, so
`𝓕 (mms_Phi s γS k)` is pointwise dominated by `(F ⋆ u)` with
`F η = ‖2^{|s|/2} ⟨η⟩^{|s|} 𝓕γ(η)‖` and `u y = ‖𝓕k(y)‖`, whence the claimed bound with the
constant `∫ F` by Young's inequality (`young_l1_l2_eLpNorm`).
-/
import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import Submission.Work.EllipticEst.InteriorRegularity.MulSobolevDefs
import Submission.Work.EllipticEst.InteriorRegularity.peetre
import Submission.Work.EllipticEst.InteriorRegularity.fourier_smulLeftCLM_eq_convolution
import Submission.Work.EllipticEst.InteriorRegularity.young_l1_l2
import Submission.Work.EllipticEst.InteriorRegularity.young_l1_l2_eLpNorm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FourierTransform MeasureTheory Filter
open scoped SchwartzMap BesselPotentialSpace ENNReal Topology

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.EllipticEst.InteriorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## Elementary norm facts -/

/-- The `ℝ≥0∞`-valued norm of a complex number is `ofReal` of its norm. -/
lemma enorm_complex_eq_ofReal (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq, show (↑(‖z‖₊) : ℝ) = ‖z‖ from rfl]

/-- The norm of a real number seen as a complex number is its absolute value. -/
lemma norm_ofReal_complex (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  have h1 : (0 : ℝ) ≤ ‖((r : ℝ) : ℂ)‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ |r| := abs_nonneg r
  nlinarith [h, sq_abs r]

/-- Peetre's inequality, in the form used for the Fourier multiplier estimate:
`⟨ξ⟩^s ⟨y⟩^{-s} ≤ 2^{|s|/2} ⟨ξ - y⟩^{|s|}`. -/
lemma mms_weight_le (s : ℝ) (ξ y : E) :
    (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖y‖ ^ 2) ^ (-s / 2)
      ≤ 2 ^ (|s| / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2) := by
  have hp : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by positivity
  have h := peetre s ξ y
  have hnp : 0 ≤ (1 + ‖y‖ ^ 2) ^ (-s / 2) := le_of_lt (Real.rpow_pos_of_pos hp _)
  have hde : (1 + ‖y‖ ^ 2) ^ (s / 2) * (1 + ‖y‖ ^ 2) ^ (-s / 2) = 1 := by
    rw [← Real.rpow_add hp, show s / 2 + -s / 2 = 0 by ring, Real.rpow_zero]
  have h2 := mul_le_mul_of_nonneg_right h hnp
  refine h2.trans_eq ?_
  calc 2 ^ (|s| / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2) * (1 + ‖y‖ ^ 2) ^ (s / 2)
        * (1 + ‖y‖ ^ 2) ^ (-s / 2)
      = 2 ^ (|s| / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2)
          * ((1 + ‖y‖ ^ 2) ^ (s / 2) * (1 + ‖y‖ ^ 2) ^ (-s / 2)) := by ring
    _ = 2 ^ (|s| / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2) := by rw [hde, mul_one]

/-! ## The Fourier side of `mms_Phi` -/

/-- Pointwise formula for the Fourier transform of `mms_Phi s γS k`. -/
lemma mms_fourier_Phi_eq (s : ℝ) (γS k : 𝓢(E, ℂ)) (ξ : E) :
    FourierTransform.fourier (⇑(mms_Phi s γS k)) ξ
      = mms_wfun (E := E) s ξ * ∫ η, FourierTransform.fourier (⇑γS) η *
          (mms_wfun (E := E) (-s) (ξ - η) * FourierTransform.fourier (⇑k) (ξ - η)) := by
  rw [← SchwartzMap.fourier_coe (mms_Phi s γS k)]
  have h1 : (FourierTransform.fourier (mms_Phi s γS k) : 𝓢(E, ℂ))
      = SchwartzMap.smulLeftCLM ℂ (mms_wfun (E := E) s)
          (FourierTransform.fourier (SchwartzMap.smulLeftCLM ℂ (⇑γS)
            (SchwartzMap.fourierMultiplierCLM ℂ (mms_wfun (E := E) (-s)) k))) := by
    rw [mms_Phi,
      mms_fourier_fourierMultiplier (mms_wfun (E := E) s) (mms_wfun_temperate s)]
  have h2 : ⇑(FourierTransform.fourier (SchwartzMap.smulLeftCLM ℂ (⇑γS)
        (SchwartzMap.fourierMultiplierCLM ℂ (mms_wfun (E := E) (-s)) k)) : 𝓢(E, ℂ))
      = fun ζ => ∫ η, FourierTransform.fourier (⇑γS) η *
        ⇑(FourierTransform.fourier (SchwartzMap.fourierMultiplierCLM ℂ (mms_wfun (E := E) (-s)) k)
          : 𝓢(E, ℂ)) (ζ - η) :=
    fourier_smulLeftCLM_eq_convolution γS _
  have h3 : ⇑(FourierTransform.fourier
        (SchwartzMap.fourierMultiplierCLM ℂ (mms_wfun (E := E) (-s)) k) : 𝓢(E, ℂ))
      = fun ζ => mms_wfun (-s) ζ * FourierTransform.fourier (⇑k) ζ := by
    rw [mms_fourier_fourierMultiplier (mms_wfun (E := E) (-s)) (mms_wfun_temperate (-s))]
    funext ζ
    rw [SchwartzMap.smulLeftCLM_apply_apply (mms_wfun_temperate (-s)), smul_eq_mul,
      SchwartzMap.fourier_coe k]
  rw [h1, SchwartzMap.smulLeftCLM_apply_apply (mms_wfun_temperate s), h2, h3]
  rw [smul_eq_mul]

/-! ## The pointwise `ℝ≥0∞`-bound -/

/-- Pointwise domination of `‖𝓕(mms_Phi s γS k)(ξ)‖` by the `ℝ≥0∞`-integral of the
convolution kernel against `‖𝓕k‖`. -/
lemma mms_Phi_enorm_le (s : ℝ) (γS k : 𝓢(E, ℂ)) (ξ : E) :
    ‖FourierTransform.fourier (⇑(mms_Phi s γS k)) ξ‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal
          (‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
              (mms_wfun (E := E) |s| (ξ - y) * FourierTransform.fourier (⇑γS) (ξ - y))‖ *
            ‖FourierTransform.fourier (⇑k) y‖) ∂(volume : Measure E) := by
  have hkey : FourierTransform.fourier (⇑(mms_Phi s γS k)) ξ
      = ∫ η, (mms_wfun (E := E) s ξ * FourierTransform.fourier (⇑γS) η) *
          (mms_wfun (E := E) (-s) (ξ - η) * FourierTransform.fourier (⇑k) (ξ - η)) := by
    rw [mms_fourier_Phi_eq s γS k ξ, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun η => by ring)
  rw [hkey]
  calc ‖∫ η, (mms_wfun (E := E) s ξ * FourierTransform.fourier (⇑γS) η) *
          (mms_wfun (E := E) (-s) (ξ - η) * FourierTransform.fourier (⇑k) (ξ - η))‖ₑ
      ≤ ∫⁻ η, ‖(mms_wfun (E := E) s ξ * FourierTransform.fourier (⇑γS) η) *
          (mms_wfun (E := E) (-s) (ξ - η) * FourierTransform.fourier (⇑k) (ξ - η))‖ₑ
            ∂(volume : Measure E) :=
        enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ η, ‖(mms_wfun (E := E) s ξ * FourierTransform.fourier (⇑γS) η)‖ₑ *
          ‖(mms_wfun (E := E) (-s) (ξ - η) * FourierTransform.fourier (⇑k) (ξ - η))‖ₑ
            ∂(volume : Measure E) := by
        refine lintegral_congr fun η => ?_
        rw [enorm_mul]
    _ = ∫⁻ y, ‖(mms_wfun (E := E) s ξ * FourierTransform.fourier (⇑γS) (ξ - y))‖ₑ *
          ‖(mms_wfun (E := E) (-s) y * FourierTransform.fourier (⇑k) y)‖ₑ
            ∂(volume : Measure E) := by
        rw [← lintegral_sub_left_eq_self (fun η =>
          ‖(mms_wfun (E := E) s ξ * FourierTransform.fourier (⇑γS) η)‖ₑ *
          ‖(mms_wfun (E := E) (-s) (ξ - η) * FourierTransform.fourier (⇑k) (ξ - η))‖ₑ) ξ]
        refine lintegral_congr fun y => ?_
        simp only [sub_sub_cancel]
    _ ≤ ∫⁻ y, ENNReal.ofReal
          (‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
              (mms_wfun (E := E) |s| (ξ - y) * FourierTransform.fourier (⇑γS) (ξ - y))‖ *
            ‖FourierTransform.fourier (⇑k) y‖) ∂(volume : Measure E) := by
        refine lintegral_mono fun y => ?_
        have h1 : ‖(mms_wfun (E := E) s ξ * FourierTransform.fourier (⇑γS) (ξ - y))‖ₑ
            = ENNReal.ofReal
                (‖mms_wfun (E := E) s ξ‖ * ‖FourierTransform.fourier (⇑γS) (ξ - y)‖) := by
          rw [enorm_mul, enorm_complex_eq_ofReal, enorm_complex_eq_ofReal,
            ← ENNReal.ofReal_mul (norm_nonneg _)]
        have h2 : ‖(mms_wfun (E := E) (-s) y * FourierTransform.fourier (⇑k) y)‖ₑ
            = ENNReal.ofReal
                (‖mms_wfun (E := E) (-s) y‖ * ‖FourierTransform.fourier (⇑k) y‖) := by
          rw [enorm_mul, enorm_complex_eq_ofReal, enorm_complex_eq_ofReal,
            ← ENNReal.ofReal_mul (norm_nonneg _)]
        rw [h1, h2, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hFs : ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
              (mms_wfun (E := E) |s| (ξ - y) * FourierTransform.fourier (⇑γS) (ξ - y))‖
            = 2 ^ (|s| / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2) *
              ‖FourierTransform.fourier (⇑γS) (ξ - y)‖ := by
          rw [norm_mul, norm_ofReal_complex, abs_of_nonneg (Real.rpow_nonneg (by norm_num) _),
            norm_mul, mms_norm_wfun]
          ring
        rw [hFs, mms_norm_wfun s ξ, mms_norm_wfun (-s) y]
        have hle := mms_weight_le s ξ y
        have hB : 0 ≤ ‖FourierTransform.fourier (⇑γS) (ξ - y)‖ := norm_nonneg _
        have hD : 0 ≤ ‖FourierTransform.fourier (⇑k) y‖ := norm_nonneg _
        have hmain : (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖y‖ ^ 2) ^ (-s / 2) *
              (‖FourierTransform.fourier (⇑γS) (ξ - y)‖ *
                ‖FourierTransform.fourier (⇑k) y‖)
            ≤ (2 ^ (|s| / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2)) *
              (‖FourierTransform.fourier (⇑γS) (ξ - y)‖ *
                ‖FourierTransform.fourier (⇑k) y‖) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg hB hD)
        calc (1 + ‖ξ‖ ^ 2) ^ (s / 2) * ‖FourierTransform.fourier (⇑γS) (ξ - y)‖ *
              ((1 + ‖y‖ ^ 2) ^ (-s / 2) * ‖FourierTransform.fourier (⇑k) y‖)
            = (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖y‖ ^ 2) ^ (-s / 2) *
              (‖FourierTransform.fourier (⇑γS) (ξ - y)‖ *
                ‖FourierTransform.fourier (⇑k) y‖) := by ring
          _ ≤ (2 ^ (|s| / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2)) *
              (‖FourierTransform.fourier (⇑γS) (ξ - y)‖ *
                ‖FourierTransform.fourier (⇑k) y‖) := hmain
          _ = 2 ^ (|s| / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2) *
              ‖FourierTransform.fourier (⇑γS) (ξ - y)‖ *
              ‖FourierTransform.fourier (⇑k) y‖ := by ring

/-! ## The estimate -/

theorem mms_Phi_estimate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (s : ℝ)
    (γS k : SchwartzMap E ℂ) :
    ‖(Work.EllipticEst.InteriorRegularity.mms_Phi s γS k).toLp 2 MeasureTheory.volume‖
      ≤ (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
            (Work.EllipticEst.InteriorRegularity.mms_wfun |s| ξ *
              FourierTransform.fourier γS ξ)‖) *
          ‖k.toLp 2 MeasureTheory.volume‖ := by
  have hFnn : ∀ z : E, 0 ≤ ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| z * FourierTransform.fourier γS z)‖ := fun _ => norm_nonneg _
  have hun : ∀ y : E, 0 ≤ ‖FourierTransform.fourier k y‖ := fun _ => norm_nonneg _
  have hFi : Integrable (fun z : E => ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| z * FourierTransform.fourier γS z)‖) (volume : Measure E) := by
    have hSint : Integrable (fun z : E =>
        ‖⇑(SchwartzMap.smulLeftCLM ℂ (mms_wfun (E := E) |s|)
          (FourierTransform.fourier γS : 𝓢(E, ℂ))) z‖) (volume : Measure E) :=
      (SchwartzMap.integrable _).norm
    refine (hSint.mul_const (2 ^ (|s| / 2))).congr (Eventually.of_forall fun z => ?_)
    dsimp only
    rw [SchwartzMap.smulLeftCLM_apply_apply (mms_wfun_temperate (E := E) |s|), smul_eq_mul,
      norm_mul, norm_mul, norm_mul, norm_ofReal_complex,
      abs_of_nonneg (Real.rpow_nonneg (by norm_num) (|s| / 2))]
    ring
  have huM : MemLp (fun y : E => ‖FourierTransform.fourier k y‖) 2 (volume : Measure E) :=
    (SchwartzMap.memLp (FourierTransform.fourier k) 2 (volume : Measure E)).norm
  have hfm : AEStronglyMeasurable
      (⇑(FourierTransform.fourier (mms_Phi s γS k))) (volume : Measure E) :=
    (SchwartzMap.memLp (FourierTransform.fourier (mms_Phi s γS k)) 2
      (volume : Measure E)).aestronglyMeasurable
  have hpt : ∀ ξ : E, ‖(⇑(FourierTransform.fourier (mms_Phi s γS k))) ξ‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal ((‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
          (mms_wfun (E := E) |s| (ξ - y) * FourierTransform.fourier γS (ξ - y))‖) *
          ‖FourierTransform.fourier k y‖) ∂(volume : Measure E) :=
    fun ξ => mms_Phi_enorm_le s γS k ξ
  have hmain := young_l1_l2_eLpNorm
    (F := fun z : E => ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| z * FourierTransform.fourier γS z)‖)
    (u := fun y : E => ‖FourierTransform.fourier k y‖)
    (f := ⇑(FourierTransform.fourier (mms_Phi s γS k))) hFnn hun hFi huM hfm hpt
  have hPhi : ‖(mms_Phi s γS k).toLp 2 (volume : Measure E)‖
      = (eLpNorm (⇑(FourierTransform.fourier (mms_Phi s γS k))) 2
          (volume : Measure E)).toReal := by
    have h1 : ‖(mms_Phi s γS k).toLp 2 (volume : Measure E)‖
        = ‖(FourierTransform.fourier (mms_Phi s γS k)).toLp 2 (volume : Measure E)‖ := by
      rw [← MeasureTheory.Lp.norm_fourier_eq ((mms_Phi s γS k).toLp 2 (volume : Measure E)),
        SchwartzMap.toLp_fourier_eq]
    rw [h1, SchwartzMap.norm_toLp]
  have hk : ‖k.toLp 2 (volume : Measure E)‖
      = (eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E)).toReal := by
    have h1 : ‖k.toLp 2 (volume : Measure E)‖
        = ‖(FourierTransform.fourier k).toLp 2 (volume : Measure E)‖ := by
      rw [← MeasureTheory.Lp.norm_fourier_eq (k.toLp 2 (volume : Measure E)),
        SchwartzMap.toLp_fourier_eq]
    rw [h1, SchwartzMap.norm_toLp]
  have hnormu : eLpNorm (fun y : E => ‖FourierTransform.fourier k y‖) 2 (volume : Measure E)
      = eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E) :=
    eLpNorm_norm _ (SchwartzMap.memLp (FourierTransform.fourier k) 2
      (volume : Measure E)).aestronglyMeasurable
  have hne : ENNReal.ofReal (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
        (mms_wfun (E := E) |s| ξ * FourierTransform.fourier γS ξ)‖)
        * eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt (SchwartzMap.memLp
      (FourierTransform.fourier k) 2 (volume : Measure E)).eLpNorm_lt_top)
  rw [hPhi, hk]
  calc (eLpNorm (⇑(FourierTransform.fourier (mms_Phi s γS k))) 2
          (volume : Measure E)).toReal
      ≤ (ENNReal.ofReal (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
            (mms_wfun (E := E) |s| ξ * FourierTransform.fourier γS ξ)‖)
          * eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E)).toReal :=
        ENNReal.toReal_mono hne (by rw [← hnormu]; exact hmain)
    _ = (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
            (mms_wfun (E := E) |s| ξ * FourierTransform.fourier γS ξ)‖)
          * (eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]

end Work.EllipticEst.InteriorRegularity
