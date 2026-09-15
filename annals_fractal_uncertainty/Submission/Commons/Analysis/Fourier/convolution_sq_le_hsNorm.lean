import Mathlib
import Submission.Commons.Measure.Integral.integral_convolution_rpow_le
import Submission.Commons.Analysis.Convolution.eLpNorm_convolution_le
import Submission.Commons.Analysis.Fourier.norm_sum_sq_le_of_bounded_overlap
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral

open MeasureTheory FourierTransform
open scoped ENNReal BigOperators FourierTransform Topology

set_option maxHeartbeats 1000000

namespace Commons.Analysis.Fourier

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The pointwise convolution `x ↦ ∫ y, g y * φ (x - y)`. -/
noncomputable def convFun (g φ : 𝔼 → ℂ) : 𝔼 → ℂ := fun x => ∫ y, g y * φ (x - y)

/-- The `ℝ≥0∞`-valued convolution majorant `∫⁻ y, ‖g y‖ₑ * ‖φ (x - y)‖ₑ`. -/
noncomputable def convMajorant (g φ : 𝔼 → ℂ) : 𝔼 → ℝ≥0∞ :=
  fun x => ∫⁻ y, ‖g y‖ₑ * ‖φ (x - y)‖ₑ

lemma convMajorant_aemeasurable (g φ : 𝔼 → ℂ) (hg : AEMeasurable (fun y : 𝔼 => ‖g y‖ₑ) volume)
    (hφ : AEMeasurable (fun y : 𝔼 => ‖φ y‖ₑ) volume) :
    AEMeasurable (convMajorant g φ) volume := by
  have hz : AEMeasurable (fun z : 𝔼 × 𝔼 => ‖g z.2‖ₑ * ‖φ (z.1 - z.2)‖ₑ) (volume.prod volume) := by
    refine hg.comp_snd.mul ?_
    exact hφ.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant volume volume)
  exact hz.lintegral_prod_right'

lemma convMajorant_eq (g φ : 𝔼 → ℂ) :
    convMajorant g φ = fun x => ∫⁻ y, ‖φ (x - y)‖ₑ * ‖g y‖ₑ := by
  funext x
  exact lintegral_congr (fun y => mul_comm _ _)

/-- `∫⁻ y, ‖g y‖ₑ‖φ(x-y)‖ₑ < ∞` for almost every `x`, when `g ∈ L²` and `φ ∈ L¹`. -/
theorem ae_convMajorant_lt_top {g φ : 𝔼 → ℂ} (hg : MemLp g 2 volume) (hφ : Integrable φ) :
    ∀ᵐ x ∂(volume : Measure 𝔼), convMajorant g φ x < ⊤ := by
  have hKm : AEMeasurable (fun y : 𝔼 => ‖φ y‖ₑ) volume := hφ.1.aemeasurable.enorm
  have hΦm : AEMeasurable (fun y : 𝔼 => ‖g y‖ₑ) volume := hg.1.aemeasurable.enorm
  have hmain := Commons.Analysis.Convolution.eLpNorm_convolution_le_ennreal
    (μ := (volume : Measure 𝔼)) (K := fun y : 𝔼 => ‖φ y‖ₑ) (Φ := fun y : 𝔼 => ‖g y‖ₑ)
    (p := 2) (q := 2) (r := 1) (by norm_num) (by norm_num) (by norm_num) hKm hΦm
  simp only [eLpNorm_enorm] at hmain
  have hφlt : eLpNorm φ (ENNReal.ofReal 1) volume < ⊤ := by
    rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm]
    exact hφ.2
  have hglt : eLpNorm g (ENNReal.ofReal 2) volume < ⊤ := by
    simpa using hg.2
  have hWlt : eLpNorm (convMajorant g φ) (ENNReal.ofReal 2) volume < ⊤ := by
    rw [convMajorant_eq]
    exact lt_of_le_of_lt hmain (ENNReal.mul_lt_top hφlt hglt)
  have hint := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := ENNReal.ofReal 2)
    (by norm_num) (by norm_num) hWlt
  simp only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 2)] at hint
  have hmeas : AEMeasurable (fun x : 𝔼 => ‖convMajorant g φ x‖ₑ ^ (2:ℝ)) volume :=
    (convMajorant_aemeasurable g φ hΦm hKm).enorm.pow_const _
  refine (ae_lt_top' hmeas (ne_of_lt hint)).mono (fun x hx => ?_)
  have hx' : convMajorant g φ x * convMajorant g φ x < ⊤ := by
    simpa only [enorm_eq_self, ENNReal.rpow_two, pow_two] using hx
  rcases ENNReal.mul_lt_top_iff.mp hx' with ⟨h, _⟩ | h | h
  · exact h
  · rw [h]; exact ENNReal.zero_lt_top
  · rw [h]; exact ENNReal.zero_lt_top

lemma ae_convolution_integrable {g φ : 𝔼 → ℂ} (hg : MemLp g 2 volume) (hφ : Integrable φ) :
    ∀ᵐ x ∂(volume : Measure 𝔼), Integrable (fun y => g y * φ (x - y)) volume := by
  have hφaesm : AEStronglyMeasurable φ volume := hφ.1
  filter_upwards [ae_convMajorant_lt_top (φ := φ) hg hφ] with x hx
  have hsub : AEStronglyMeasurable (fun y : 𝔼 => φ (x - y)) volume :=
    hφaesm.comp_quasiMeasurePreserving (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving
  refine ⟨hg.1.mul hsub, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  have hE : ∫⁻ y, ‖g y * φ (x - y)‖ₑ ∂volume = convMajorant g φ x := by
    rw [convMajorant]
    exact lintegral_congr (fun y => by rw [enorm_mul])
  rw [hE]
  exact hx

lemma aestronglyMeasurable_convFun {g φ : 𝔼 → ℂ} (hg : AEStronglyMeasurable g volume)
    (hφ : AEStronglyMeasurable φ volume) : AEStronglyMeasurable (convFun g φ) volume := by
  have h1 : AEStronglyMeasurable (fun p : 𝔼 × 𝔼 => g p.2 * φ (p.1 - p.2)) (volume.prod volume) := by
    have h := hg.convolution_integrand (L := ContinuousLinearMap.mul ℂ ℂ) hφ
    simpa only [ContinuousLinearMap.mul_apply'] using h
  exact h1.integral_prod_right'

/-- Young's inequality at the level of `eLpNorm` for the convolution function. -/
theorem eLpNorm_convFun_le {g φ : 𝔼 → ℂ} (hg : MemLp g 2 volume) (hφ : Integrable φ) :
    eLpNorm (convFun g φ) 2 volume ≤ eLpNorm g 2 volume * eLpNorm φ 1 volume := by
  have hpoint : ∀ x : 𝔼, ‖convFun g φ x‖ₑ ≤ ‖convMajorant g φ x‖ₑ := fun x =>
    le_trans (enorm_integral_le_lintegral_enorm _)
      (le_of_eq (lintegral_congr (fun y => by rw [enorm_mul])))
  have h1 : eLpNorm (convFun g φ) 2 volume ≤ eLpNorm (convMajorant g φ) 2 volume :=
    eLpNorm_mono_enorm_ae (f := convFun g φ) (g := convMajorant g φ)
      (Filter.Eventually.of_forall hpoint)
  refine h1.trans ?_
  have hKm : AEMeasurable (fun y : 𝔼 => ‖φ y‖ₑ) volume := hφ.1.aemeasurable.enorm
  have hΦm : AEMeasurable (fun y : 𝔼 => ‖g y‖ₑ) volume := hg.1.aemeasurable.enorm
  have hmain := Commons.Analysis.Convolution.eLpNorm_convolution_le_ennreal
    (μ := (volume : Measure 𝔼)) (K := fun y : 𝔼 => ‖φ y‖ₑ) (Φ := fun y : 𝔼 => ‖g y‖ₑ)
    (p := 2) (q := 2) (r := 1) (by norm_num) (by norm_num) (by norm_num) hKm hΦm
  simp only [eLpNorm_enorm, ENNReal.ofReal_ofNat, ENNReal.ofReal_one] at hmain
  have hconv : (fun x : 𝔼 => ∫⁻ y, ‖φ (x - y)‖ₑ * ‖g y‖ₑ) = convMajorant g φ := by
    funext x
    rw [convMajorant]
    exact lintegral_congr (fun y => mul_comm _ _)
  rw [hconv] at hmain
  exact hmain.trans (le_of_eq (mul_comm _ _))

theorem memLp_convFun_two {g φ : 𝔼 → ℂ} (hg : MemLp g 2 volume) (hφ : Integrable φ) :
    MemLp (convFun g φ) 2 volume :=
  ⟨aestronglyMeasurable_convFun hg.1 hφ.1,
    lt_of_le_of_lt (eLpNorm_convFun_le hg hφ)
      (ENNReal.mul_lt_top hg.2 (by
        rw [eLpNorm_one_eq_lintegral_enorm]; exact hφ.2))⟩

/-- Almost-everywhere additivity of the convolution function. -/
theorem convFun_sub_ae {g h φ : 𝔼 → ℂ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    (hφ : Integrable φ) :
    convFun (g - h) φ =ᵐ[volume] fun x => convFun g φ x - convFun h φ x := by
  filter_upwards [ae_convolution_integrable hg hφ, ae_convolution_integrable hh hφ] with x hgx hhx
  have : (∫ y, (g - h) y * φ (x - y)) = (∫ y, g y * φ (x - y)) - (∫ y, h y * φ (x - y)) := by
    rw [← MeasureTheory.integral_sub hgx hhx]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]; ring
  exact this

theorem eLpNorm_convFun_sub_le {g h φ : 𝔼 → ℂ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    (hφ : Integrable φ) :
    eLpNorm (fun x => convFun g φ x - convFun h φ x) 2 volume
      ≤ eLpNorm (g - h) 2 volume * eLpNorm φ 1 volume := by
  have hpoint : ∀ᵐ x ∂(volume : Measure 𝔼),
      ‖convFun g φ x - convFun h φ x‖ₑ ≤ ‖convMajorant (g - h) φ x‖ₑ := by
    filter_upwards [convFun_sub_ae hg hh hφ] with x hx
    rw [← hx]
    refine le_trans (enorm_integral_le_lintegral_enorm _) (le_of_eq ?_)
    exact lintegral_congr (fun y => by rw [enorm_mul])
  refine (eLpNorm_mono_enorm_ae (f := fun x => convFun g φ x - convFun h φ x)
    (g := convMajorant (g - h) φ) hpoint).trans ?_
  have hKm : AEMeasurable (fun y : 𝔼 => ‖φ y‖ₑ) volume := hφ.1.aemeasurable.enorm
  have hΦm : AEMeasurable (fun y : 𝔼 => ‖(g - h) y‖ₑ) volume := (hg.sub hh).1.aemeasurable.enorm
  have hmain := Commons.Analysis.Convolution.eLpNorm_convolution_le_ennreal
    (μ := (volume : Measure 𝔼)) (K := fun y : 𝔼 => ‖φ y‖ₑ) (Φ := fun y : 𝔼 => ‖(g - h) y‖ₑ)
    (p := 2) (q := 2) (r := 1) (by norm_num) (by norm_num) (by norm_num) hKm hΦm
  simp only [eLpNorm_enorm, ENNReal.ofReal_ofNat, ENNReal.ofReal_one] at hmain
  have hconv : (fun x : 𝔼 => ∫⁻ y, ‖φ (x - y)‖ₑ * ‖(g - h) y‖ₑ) = convMajorant (g - h) φ := by
    funext x
    rw [convMajorant]
    exact lintegral_congr (fun y => mul_comm _ _)
  rw [hconv] at hmain
  exact hmain.trans (le_of_eq (mul_comm _ _))

end Commons.Analysis.Fourier

namespace Commons.Analysis.Fourier
open MeasureTheory

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

theorem enorm_fourier_lp (X : Lp ℂ 2 (volume : Measure 𝔼)) : ‖𝓕 X‖ₑ = ‖X‖ₑ := by
  have h : ‖𝓕 X‖ = ‖X‖ := MeasureTheory.Lp.norm_fourier_eq X
  rw [MeasureTheory.Lp.enorm_def, MeasureTheory.Lp.enorm_def]
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def] at h
  rcases (ENNReal.toReal_eq_toReal_iff _ _).mp h with h' | ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact h'
  · exact absurd h2 (MeasureTheory.Lp.eLpNorm_ne_top X)
  · exact absurd h1 (MeasureTheory.Lp.eLpNorm_ne_top _)

theorem eLpNorm_coeFn_fourier (X : Lp ℂ 2 (volume : Measure 𝔼)) :
    eLpNorm ((𝓕 X : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) 2 volume
      = eLpNorm (X : 𝔼 → ℂ) 2 volume := by
  rw [← MeasureTheory.Lp.enorm_def, ← MeasureTheory.Lp.enorm_def]
  exact enorm_fourier_lp X

theorem toReal_eLpNorm_two_sq {h : 𝔼 → ℂ} (h2 : MemLp h 2 volume) :
    (eLpNorm h 2 volume).toReal ^ 2 = ∫ x, ‖h x‖ ^ 2 := by
  have heq : eLpNorm h 2 volume = eLpNorm ((h2.toLp h : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) 2 volume :=
    (eLpNorm_congr_ae h2.coeFn_toLp).symm
  rw [heq, ← MeasureTheory.Lp.norm_def]
  rw [← Commons.Analysis.Fourier.lp_integral_norm_sq (h2.toLp h)]
  exact integral_congr_ae (h2.coeFn_toLp.mono (fun x hx => by simp only [hx]))

/-- `(1 + ‖ξ‖²)^{-d/2}`. -/
noncomputable def mfun (ξ : 𝔼) : ℝ := (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2)

lemma mfun_nonneg (ξ : 𝔼) : 0 ≤ mfun ξ := by
  rw [mfun]
  exact Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 1 + ‖ξ‖ ^ 2) _

lemma mfun_le_one (ξ : 𝔼) : mfun ξ ≤ 1 := by
  rw [mfun]
  have h1 : (1:ℝ) ≤ 1 + ‖ξ‖^2 := by
    have := sq_nonneg ‖ξ‖; linarith
  have h2 : -(d:ℝ)/2 ≤ 0 := by
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    linarith
  calc (1 + ‖ξ‖^2) ^ (-(d:ℝ)/2) ≤ (1 + ‖ξ‖^2) ^ (0:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 h2
    _ = 1 := Real.rpow_zero _

lemma mfun_sq (ξ : 𝔼) : mfun ξ ^ 2 = (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) := by
  rw [mfun]
  rw [sq, ← Real.rpow_add (by positivity : (0:ℝ) < 1 + ‖ξ‖ ^ 2)]
  congr 1
  ring

end Commons.Analysis.Fourier

namespace Commons.Analysis.Fourier
open MeasureTheory

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

theorem eLpNorm_convFun_le_one {g φ : 𝔼 → ℂ} (h1 : MemLp g 1 volume) (hφ : Integrable φ) :
    eLpNorm (convFun g φ) 1 volume ≤ eLpNorm g 1 volume * eLpNorm φ 1 volume := by
  have hpoint : ∀ x : 𝔼, ‖convFun g φ x‖ₑ ≤ ‖convMajorant g φ x‖ₑ := fun x =>
    le_trans (enorm_integral_le_lintegral_enorm _)
      (le_of_eq (lintegral_congr (fun y => by rw [enorm_mul])))
  refine (eLpNorm_mono_enorm_ae (f := convFun g φ) (g := convMajorant g φ)
    (Filter.Eventually.of_forall hpoint)).trans ?_
  have hKm : AEMeasurable (fun y : 𝔼 => ‖φ y‖ₑ) volume := hφ.1.aemeasurable.enorm
  have hΦm : AEMeasurable (fun y : 𝔼 => ‖g y‖ₑ) volume := h1.1.aemeasurable.enorm
  have hmain := Commons.Analysis.Convolution.eLpNorm_convolution_le_ennreal
    (μ := (volume : Measure 𝔼)) (K := fun y : 𝔼 => ‖φ y‖ₑ) (Φ := fun y : 𝔼 => ‖g y‖ₑ)
    (p := 1) (q := 1) (r := 1) (by norm_num) (by norm_num) (by norm_num) hKm hΦm
  simp only [eLpNorm_enorm, ENNReal.ofReal_one] at hmain
  have hconv : (fun x : 𝔼 => ∫⁻ y, ‖φ (x - y)‖ₑ * ‖g y‖ₑ) = convMajorant g φ := by
    funext x
    rw [convMajorant]
    exact lintegral_congr (fun y => mul_comm _ _)
  rw [hconv] at hmain
  exact hmain.trans (le_of_eq (mul_comm _ _))

theorem memLp_convFun_one {g φ : 𝔼 → ℂ} (h1 : MemLp g 1 volume) (hφ : Integrable φ) :
    MemLp (convFun g φ) 1 volume := by
  refine ⟨aestronglyMeasurable_convFun h1.1 hφ.1, lt_of_le_of_lt (eLpNorm_convFun_le_one h1 hφ) ?_⟩
  refine ENNReal.mul_lt_top h1.2 ?_
  rw [eLpNorm_one_eq_lintegral_enorm]; exact hφ.2

theorem fourier_convFun {g φ : 𝔼 → ℂ} (hφ : Integrable φ) (hg : Integrable g) (ξ : 𝔼) :
    𝓕 (convFun g φ) ξ = 𝓕 φ ξ * 𝓕 g ξ := by
  have h : convFun g φ = MeasureTheory.convolution g φ (ContinuousLinearMap.lsmul ℂ ℂ) volume := by
    funext x
    rw [convFun, MeasureTheory.convolution_def]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun t => by
        simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul])
  rw [h, Real.fourier_smul_convolution_eq hg hφ ξ, smul_eq_mul, mul_comm]

/-- The `L¹ ∩ L²` case of the Fourier-side inequality for the convolution. -/
theorem eLpNorm_convFun_le_fourier {g φ : 𝔼 → ℂ} (h1 : MemLp g 1 volume) (h2 : MemLp g 2 volume)
    (hφ : Integrable φ) (hψ : ∀ ξ : 𝔼, ‖𝓕 φ ξ‖ ≤ mfun ξ) :
    eLpNorm (convFun g φ) 2 volume
      ≤ eLpNorm (fun ξ => mfun ξ
          * ((𝓕 (h2.toLp g) : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ) 2 volume := by
  have hgint : Integrable g := memLp_one_iff_integrable.mp h1
  have hc2 : MemLp (convFun g φ) 2 volume := memLp_convFun_two h2 hφ
  have hc1 : MemLp (convFun g φ) 1 volume := memLp_convFun_one h1 hφ
  have hstep1 : eLpNorm (convFun g φ) 2 volume
      = eLpNorm (fun ξ : 𝔼 => 𝓕 (convFun g φ) ξ) 2 volume := by
    rw [← eLpNorm_congr_ae hc2.coeFn_toLp, ← eLpNorm_coeFn_fourier (hc2.toLp (convFun g φ)),
        eLpNorm_congr_ae (fourier_toLp_ae_eq_fourier_of_memLp hc1 hc2)]
  have hstep2 : eLpNorm (fun ξ : 𝔼 => 𝓕 (convFun g φ) ξ) 2 volume
      = eLpNorm (fun ξ : 𝔼 => 𝓕 φ ξ * 𝓕 g ξ) 2 volume := by
    rw [show (fun ξ : 𝔼 => 𝓕 (convFun g φ) ξ) = (fun ξ : 𝔼 => 𝓕 φ ξ * 𝓕 g ξ) from
      funext (fourier_convFun hφ hgint)]
  have hstep3 : eLpNorm (fun ξ : 𝔼 => 𝓕 φ ξ * 𝓕 g ξ) 2 volume
      ≤ eLpNorm (fun ξ : 𝔼 => mfun ξ * 𝓕 g ξ) 2 volume := by
    refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun ξ => ?_)
    have hm : ‖((mfun ξ : ℝ) : ℂ)‖ = mfun ξ := by
      rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq (mfun_nonneg ξ)]
    rw [norm_mul, norm_mul, hm]
    exact mul_le_mul_of_nonneg_right (hψ ξ) (norm_nonneg _)
  have hstep4 : eLpNorm (fun ξ : 𝔼 => mfun ξ * 𝓕 g ξ) 2 volume
      = eLpNorm (fun ξ => mfun ξ
          * ((𝓕 (h2.toLp g) : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ) 2 volume := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [(fourier_toLp_ae_eq_fourier_of_memLp h1 h2).symm] with ξ hξ
    rw [hξ]
  calc eLpNorm (convFun g φ) 2 volume
      = eLpNorm (fun ξ : 𝔼 => 𝓕 (convFun g φ) ξ) 2 volume := hstep1
    _ = eLpNorm (fun ξ : 𝔼 => 𝓕 φ ξ * 𝓕 g ξ) 2 volume := hstep2
    _ ≤ eLpNorm (fun ξ : 𝔼 => mfun ξ * 𝓕 g ξ) 2 volume := hstep3
    _ = eLpNorm (fun ξ : 𝔼 => mfun ξ
          * ((𝓕 (h2.toLp g) : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ) 2 volume := hstep4

end Commons.Analysis.Fourier

namespace Commons.Analysis.Fourier
open MeasureTheory

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma measurable_mfun : Measurable (mfun (d := d)) := by
  unfold mfun
  fun_prop

lemma aestronglyMeasurable_mfunC :
    AEStronglyMeasurable (fun ξ : 𝔼 => ((mfun ξ : ℝ) : ℂ)) volume :=
  (Complex.measurable_ofReal.comp measurable_mfun).aestronglyMeasurable

/-- On `L²`, the Fourier transform is additive. -/
lemma fourier_sub_lp (X Y : Lp ℂ 2 (volume : Measure 𝔼)) : 𝓕 (X - Y) = 𝓕 X - 𝓕 Y := by
  change (Lp.fourierTransformₗᵢ 𝔼 ℂ) (X - Y) = (Lp.fourierTransformₗᵢ 𝔼 ℂ) X - (Lp.fourierTransformₗᵢ 𝔼 ℂ) Y
  exact map_sub _ _ _

end Commons.Analysis.Fourier

namespace Commons.Analysis.Fourier
open MeasureTheory

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The Schwartz-approximation step: for a Schwartz `θ`, the convolution is controlled by the
weighted Fourier norm of `F` plus two approximation errors. -/
lemma eLpNorm_convFun_le_add_errors {f φ : 𝔼 → ℂ} (hf : MemLp f 2 volume) (hφ : Integrable φ)
    (hψ : ∀ ξ : 𝔼, ‖𝓕 φ ξ‖ ≤ mfun ξ) (θ : SchwartzMap 𝔼 ℂ) :
    eLpNorm (convFun f φ) 2 volume
      ≤ eLpNorm (fun ξ => mfun ξ * ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ)
          2 volume
        + (eLpNorm ((θ.toLp 2 volume : Lp ℂ 2 (volume : Measure 𝔼)) - hf.toLp f) 2 volume
            + eLpNorm (hf.toLp f - (θ.toLp 2 volume : Lp ℂ 2 (volume : Measure 𝔼))) 2 volume
              * eLpNorm φ 1 volume) := by
  set F : Lp ℂ 2 (volume : Measure 𝔼) := hf.toLp f with hF
  set G : Lp ℂ 2 (volume : Measure 𝔼) := (θ.toLp 2 volume : Lp ℂ 2 (volume : Measure 𝔼)) with hG
  have h1θ : MemLp (θ : 𝔼 → ℂ) 1 volume := θ.memLp 1 volume
  have h2θ : MemLp (θ : 𝔼 → ℂ) 2 volume := θ.memLp 2 volume
  have hGθ : h2θ.toLp (θ : 𝔼 → ℂ) = G := rfl
  -- Triangle inequality
  have htri : eLpNorm (convFun f φ) 2 volume
      ≤ eLpNorm (convFun (θ : 𝔼 → ℂ) φ) 2 volume
        + eLpNorm (convFun (f - (θ : 𝔼 → ℂ)) φ) 2 volume := by
    have hae : convFun f φ =ᵐ[volume]
        convFun (θ : 𝔼 → ℂ) φ + convFun (f - (θ : 𝔼 → ℂ)) φ := by
      filter_upwards [convFun_sub_ae hf h2θ hφ] with x hx
      simp only [Pi.add_apply]
      rw [hx]; ring
    refine (eLpNorm_congr_ae hae).trans_le ?_
    refine eLpNorm_add_le (memLp_convFun_two h2θ hφ).1 (memLp_convFun_two (hf.sub h2θ) hφ).1
      (by norm_num)
  -- The Schwartz bound
  have hS : eLpNorm (convFun (θ : 𝔼 → ℂ) φ) 2 volume
      ≤ eLpNorm (fun ξ => mfun ξ * ((𝓕 G : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ) 2 volume := by
    refine (eLpNorm_convFun_le_fourier h1θ h2θ hφ hψ).trans (le_of_eq ?_)
    rw [hGθ]
  -- Splitting the Fourier side
  have hsplit : eLpNorm (fun ξ => mfun ξ * ((𝓕 G : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ)
        2 volume
      ≤ eLpNorm (fun ξ => mfun ξ * ((𝓕 F : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ) 2 volume
        + eLpNorm (fun ξ => mfun ξ
            * (((𝓕 G : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ
              - ((𝓕 F : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ)) 2 volume := by
    have hae : (fun ξ : 𝔼 => mfun ξ * ((𝓕 G : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ)
        =ᵐ[volume]
        (fun ξ : 𝔼 => mfun ξ * ((𝓕 F : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ)
          + (fun ξ : 𝔼 => mfun ξ
              * (((𝓕 G : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ
                - ((𝓕 F : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ)) := by
      filter_upwards with ξ
      simp only [Pi.add_apply]
      ring
    refine (eLpNorm_congr_ae hae).trans_le ?_
    refine eLpNorm_add_le ?_ ?_ (by norm_num)
    · exact aestronglyMeasurable_mfunC.mul (Lp.aestronglyMeasurable (𝓕 F))
    · exact aestronglyMeasurable_mfunC.mul
        ((Lp.aestronglyMeasurable (𝓕 G)).sub (Lp.aestronglyMeasurable (𝓕 F)))
  -- Bounding the Fourier error by the `L²` distance
  have hD1 : eLpNorm (fun ξ => mfun ξ
        * (((𝓕 G : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ
          - ((𝓕 F : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ)) 2 volume
      ≤ eLpNorm (G - F) 2 volume := by
    have hpt : ∀ᵐ ξ ∂(volume : Measure 𝔼),
        ‖mfun ξ * (((𝓕 G : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ
          - ((𝓕 F : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ)‖
        ≤ ‖(((𝓕 G : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ
          - ((𝓕 F : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ)‖ := by
      filter_upwards with ξ
      rw [norm_mul]
      have hm : ‖((mfun ξ : ℝ) : ℂ)‖ = mfun ξ := by
        rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq (mfun_nonneg ξ)]
      rw [hm]
      calc mfun ξ * ‖_‖ ≤ 1 * ‖_‖ :=
            mul_le_mul_of_nonneg_right (mfun_le_one ξ) (norm_nonneg _)
        _ = ‖_‖ := one_mul _
    refine (eLpNorm_mono_ae hpt).trans ?_
    have h1 : (fun x : 𝔼 => ((𝓕 G : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) x
          - ((𝓕 F : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) x)
        =ᵐ[volume]
        (((𝓕 G : Lp ℂ 2 (volume : Measure 𝔼)) - (𝓕 F : Lp ℂ 2 (volume : Measure 𝔼))) :
          Lp ℂ 2 (volume : Measure 𝔼)) :=
      (Lp.coeFn_sub (𝓕 G) (𝓕 F)).symm
    rw [eLpNorm_congr_ae h1, ← fourier_sub_lp G F]
    exact le_of_eq (eLpNorm_coeFn_fourier (G - F))
  -- Bounding the convolution error by Young's inequality
  have hD2 : eLpNorm (convFun (f - (θ : 𝔼 → ℂ)) φ) 2 volume
      ≤ eLpNorm (F - G) 2 volume * eLpNorm φ 1 volume := by
    refine (eLpNorm_convFun_le (hf.sub h2θ) hφ).trans ?_
    have hae : (f - (θ : 𝔼 → ℂ)) =ᵐ[volume] ((F - G : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) := by
      filter_upwards [hf.coeFn_toLp, h2θ.coeFn_toLp, Lp.coeFn_sub F G] with ξ h1 h2 h3
      have h1' : ((F : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ = f ξ := h1
      have h2' : ((G : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ = θ ξ := h2
      simp only [Pi.sub_apply, h1', h2', h3]
    rw [eLpNorm_congr_ae hae]
  calc eLpNorm (convFun f φ) 2 volume
      ≤ eLpNorm (convFun (θ : 𝔼 → ℂ) φ) 2 volume
        + eLpNorm (convFun (f - (θ : 𝔼 → ℂ)) φ) 2 volume := htri
    _ ≤ eLpNorm (fun ξ => mfun ξ * ((𝓕 G : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ) 2 volume
        + eLpNorm (F - G) 2 volume * eLpNorm φ 1 volume :=
        add_le_add hS hD2
    _ ≤ (eLpNorm (fun ξ => mfun ξ * ((𝓕 F : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ) 2 volume
          + eLpNorm (G - F) 2 volume)
        + eLpNorm (F - G) 2 volume * eLpNorm φ 1 volume :=
        add_le_add (hsplit.trans (add_le_add le_rfl hD1)) le_rfl
    _ = eLpNorm (fun ξ => mfun ξ * ((𝓕 F : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ) 2 volume
        + (eLpNorm (G - F) 2 volume + eLpNorm (F - G) 2 volume * eLpNorm φ 1 volume) := by
        rw [add_assoc]
    _ = eLpNorm (fun ξ => mfun ξ * ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ)
          2 volume
        + (eLpNorm ((θ.toLp 2 volume : Lp ℂ 2 (volume : Measure 𝔼)) - hf.toLp f) 2 volume
            + eLpNorm (hf.toLp f - (θ.toLp 2 volume : Lp ℂ 2 (volume : Measure 𝔼))) 2 volume
              * eLpNorm φ 1 volume) := by rw [hF, hG]

end Commons.Analysis.Fourier

namespace Commons.Analysis.Fourier
open MeasureTheory Filter

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The key `eLpNorm` inequality: the `L²` norm of the convolution `f ⋆ φ` is bounded by the
weighted `L²` norm of the `L²`-Fourier transform of `f`. -/
theorem eLpNorm_convFun_le_mfun {f φ : 𝔼 → ℂ} (hf : MemLp f 2 volume) (hφ : Integrable φ)
    (hψ : ∀ ξ : 𝔼, ‖𝓕 φ ξ‖ ≤ mfun ξ) :
    eLpNorm (convFun f φ) 2 volume
      ≤ eLpNorm (fun ξ => mfun ξ * ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ)
          2 volume := by
  classical
  set F : Lp ℂ 2 (volume : Measure 𝔼) := hf.toLp f with hF
  set W : ℝ≥0∞ := eLpNorm (fun ξ => mfun ξ * ((𝓕 F : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ)
    2 volume with hW
  have hdense : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure 𝔼)) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  choose θ hθ using fun n : ℕ =>
    (Metric.denseRange_iff.mp hdense F (1 / ((n:ℝ) + 1)) (by positivity))
  have hθ' : ∀ n : ℕ, dist F ((θ n).toLp 2 volume) < 1 / ((n:ℝ) + 1) := by
    intro n; simpa using hθ n
  have hWfin : W ≠ ⊤ := by
    rw [hW]
    refine ne_of_lt (lt_of_le_of_lt ?_ (Lp.memLp (𝓕 F)).2)
    refine eLpNorm_mono_ae (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul]
    have hm : ‖((mfun ξ : ℝ) : ℂ)‖ = mfun ξ := by
      rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq (mfun_nonneg ξ)]
    rw [hm]
    calc mfun ξ * ‖_‖ ≤ 1 * ‖_‖ := mul_le_mul_of_nonneg_right (mfun_le_one ξ) (norm_nonneg _)
      _ = ‖_‖ := one_mul _
  have hbound : ∀ n : ℕ, eLpNorm (convFun f φ) 2 volume
      ≤ W + (eLpNorm ((θ n).toLp 2 volume - F) 2 volume
           + eLpNorm (F - (θ n).toLp 2 volume) 2 volume * eLpNorm φ 1 volume) := by
    intro n
    have h := eLpNorm_convFun_le_add_errors (f := f) (φ := φ) hf hφ hψ (θ n)
    have e1 : eLpNorm ((θ n).toLp 2 volume - hf.toLp f) 2 volume
        = eLpNorm ((θ n).toLp 2 volume - F) 2 volume := by rw [hF]
    have e2 : eLpNorm (hf.toLp f - (θ n).toLp 2 volume) 2 volume
        = eLpNorm (F - (θ n).toLp 2 volume) 2 volume := by rw [hF]
    have e3 : eLpNorm (fun ξ => mfun ξ * ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure 𝔼)) : 𝔼 → ℂ) ξ)
        2 volume
        = W := by rw [hW, hF]
    rw [e1, e2, e3] at h
    exact h
  set Cp : ℝ := (eLpNorm φ 1 volume).toReal with hCp
  have hφfin : eLpNorm φ 1 volume ≠ ⊤ := by
    rw [eLpNorm_one_eq_lintegral_enorm]; exact ne_of_lt hφ.2
  have hreal : ∀ n : ℕ, (eLpNorm (convFun f φ) 2 volume).toReal
      ≤ W.toReal + (dist F ((θ n).toLp 2 volume) + dist F ((θ n).toLp 2 volume) * Cp) := by
    intro n
    have h1 := hbound n
    have hfinA : eLpNorm ((θ n).toLp 2 volume - F) 2 volume ≠ ⊤ :=
      ne_of_lt (Lp.memLp ((θ n).toLp 2 volume - F)).2
    have hfinB : eLpNorm (F - (θ n).toLp 2 volume) 2 volume ≠ ⊤ :=
      ne_of_lt (Lp.memLp (F - (θ n).toLp 2 volume)).2
    have hfinX : (eLpNorm ((θ n).toLp 2 volume - F) 2 volume
        + eLpNorm (F - (θ n).toLp 2 volume) 2 volume * eLpNorm φ 1 volume) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hfinA, ENNReal.mul_ne_top hfinB hφfin⟩
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hWfin, hfinX⟩) h1
    rw [ENNReal.toReal_add hWfin hfinX,
        ENNReal.toReal_add hfinA (ENNReal.mul_ne_top hfinB hφfin),
        ENNReal.toReal_mul] at h2
    have hE1 : (eLpNorm ((θ n).toLp 2 volume - F) 2 volume).toReal
        = dist F ((θ n).toLp 2 volume) := by
      rw [dist_eq_norm, norm_sub_rev, ← Lp.norm_def]
    have hE2 : (eLpNorm (F - (θ n).toLp 2 volume) 2 volume).toReal
        = dist F ((θ n).toLp 2 volume) := by
      rw [dist_eq_norm, ← Lp.norm_def]
    rw [hE1, hE2, ← hCp] at h2
    exact h2
  have hlim : Tendsto (fun n : ℕ => dist F ((θ n).toLp 2 volume)
      + dist F ((θ n).toLp 2 volume) * Cp) atTop (𝓝 0) := by
    have hdist : Tendsto (fun n : ℕ => dist F ((θ n).toLp 2 volume)) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (hθ' n)) ?_
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h1 : Tendsto (fun n : ℕ => dist F ((θ n).toLp 2 volume) * Cp) atTop (𝓝 (0 * Cp)) :=
      hdist.mul_const Cp
    simpa using hdist.add h1
  have hAle : (eLpNorm (convFun f φ) 2 volume).toReal ≤ W.toReal :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds
      (by simpa using (tendsto_const_nhds.add hlim)) (fun n => hreal n)
  have hfinL : eLpNorm (convFun f φ) 2 volume ≠ ⊤ :=
    ne_of_lt (memLp_convFun_two hf hφ).2
  change eLpNorm (convFun f φ) 2 volume ≤ W
  exact (ENNReal.toReal_le_toReal hfinL hWfin).mp hAle

end Commons.Analysis.Fourier

namespace Commons.Analysis.Fourier
open MeasureTheory Filter

/-- The requested lemma. -/
theorem convolution_sq_le_hsNorm (d : ℕ)
    {f φ : EuclideanSpace ℝ (Fin d) → ℂ}
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hφ : MeasureTheory.Integrable φ
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hψ : ∀ ξ : EuclideanSpace ℝ (Fin d),
      ‖(FourierTransform.fourier φ) ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2)) :
    MeasureTheory.integral MeasureTheory.volume
      (fun x : EuclideanSpace ℝ (Fin d) => ‖∫ y, f y * φ (x - y)‖ ^ 2)
      ≤ MeasureTheory.integral MeasureTheory.volume
          (fun ξ : EuclideanSpace ℝ (Fin d) =>
            (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) *
              ‖((FourierTransform.fourier (hf.toLp f) : MeasureTheory.Lp ℂ 2
                (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
                  EuclideanSpace ℝ (Fin d) → ℂ) ξ‖ ^ 2) := by
  have hkey := eLpNorm_convFun_le_mfun (d := d) (f := f) (φ := φ) hf hφ hψ
  set A : ℝ := (eLpNorm (convFun f φ) 2 MeasureTheory.volume).toReal with hA
  set Bv : ℝ := (eLpNorm (fun ξ : EuclideanSpace ℝ (Fin d) => mfun ξ
      * ((FourierTransform.fourier (hf.toLp f) : MeasureTheory.Lp ℂ 2
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
            EuclideanSpace ℝ (Fin d) → ℂ) ξ) 2 MeasureTheory.volume).toReal with hBv
  have hBfin : eLpNorm (fun ξ : EuclideanSpace ℝ (Fin d) => mfun ξ
      * ((FourierTransform.fourier (hf.toLp f) : MeasureTheory.Lp ℂ 2
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
            EuclideanSpace ℝ (Fin d) → ℂ) ξ) 2 MeasureTheory.volume ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt ?_ (MeasureTheory.Lp.memLp (𝓕 (hf.toLp f))).2)
    refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun ξ => ?_)
    rw [norm_mul]
    have hm : ‖((mfun ξ : ℝ) : ℂ)‖ = mfun ξ := by
      rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq (mfun_nonneg ξ)]
    rw [hm]
    calc mfun ξ * ‖_‖ ≤ 1 * ‖_‖ := mul_le_mul_of_nonneg_right (mfun_le_one ξ) (norm_nonneg _)
      _ = ‖_‖ := one_mul _
  have hAB : A ≤ Bv := by
    rw [hA, hBv]
    exact ENNReal.toReal_mono hBfin hkey
  have hmem : MeasureTheory.MemLp (fun ξ : EuclideanSpace ℝ (Fin d) => mfun ξ
      * ((FourierTransform.fourier (hf.toLp f) : MeasureTheory.Lp ℂ 2
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
            EuclideanSpace ℝ (Fin d) → ℂ) ξ) 2 MeasureTheory.volume := by
    have hm : MeasureTheory.MemLp (fun ξ : EuclideanSpace ℝ (Fin d) => ((mfun ξ : ℝ) : ℂ))
        ⊤ MeasureTheory.volume :=
      memLp_top_of_bound aestronglyMeasurable_mfunC 1
        (Filter.Eventually.of_forall fun ξ => by
          rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq (mfun_nonneg ξ)]
          exact mfun_le_one ξ)
    have h2 := (MeasureTheory.Lp.memLp (𝓕 (hf.toLp f))).mul (p := ⊤) (r := 2) hm
    refine (MeasureTheory.memLp_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)).mp h2
    simp only [Pi.mul_apply]
  have hLHS : MeasureTheory.integral MeasureTheory.volume
      (fun x : EuclideanSpace ℝ (Fin d) => ‖∫ y, f y * φ (x - y)‖ ^ 2) = A ^ 2 := by
    rw [hA]
    rw [toReal_eLpNorm_two_sq (memLp_convFun_two hf hφ)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rfl
  have hRHS : MeasureTheory.integral MeasureTheory.volume
      (fun ξ : EuclideanSpace ℝ (Fin d) =>
        (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)) *
          ‖((FourierTransform.fourier (hf.toLp f) : MeasureTheory.Lp ℂ 2
            (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
              EuclideanSpace ℝ (Fin d) → ℂ) ξ‖ ^ 2) = Bv ^ 2 := by
    rw [hBv]
    rw [toReal_eLpNorm_two_sq hmem]
    refine (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)).symm
    rw [norm_mul]
    have hm : ‖((mfun ξ : ℝ) : ℂ)‖ = mfun ξ := by
      rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq (mfun_nonneg ξ)]
    rw [hm, mul_pow, mfun_sq]
  rw [hLHS, hRHS]
  exact pow_le_pow_left₀ (by rw [hA]; exact ENNReal.toReal_nonneg) hAB 2

end Commons.Analysis.Fourier
