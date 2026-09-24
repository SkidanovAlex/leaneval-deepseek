import Mathlib
import Submission.Work.GM.Affine.nearcorr_defs
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.norm_Fhat_conv_le

/-!
# The Fourier transform of the smoothed profile `Afun`

`Afun f M₂ K T` is the convolution of the profile `Hprof f M₂` with the rescaled smoothing
kernel `ρ(t) = s⁻¹ ψ(t/s)`, where `s = smScale K T M₂ = M₂/(2KT)` and `ψ = psiSmooth`:

  `Afun f M₂ K T v = ∫ u, Hprof f M₂ (v - s u) ψ u du = ∫ t, ρ t · Hprof f M₂ (v - t) dt`.

The convolution theorem (`Fhat_convolution_eq`) therefore gives

  `Fhat (Afun f M₂ K T) x = Fhat ρ x * Fhat (Hprof f M₂) x`,

and the scaling identity `Fhat ρ x = Fhat psiSmooth (s x)` finishes the proof.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- Change of variables `t ↦ s t` (`s > 0`) in `∫ t, s⁻¹ ψ(t/s) H(v - t) dt`. -/
lemma integral_smul_comp_mul {ψ H : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (v : ℝ) :
    (∫ t : ℝ, (1 / s) * ψ (t / s) * H (v - t)) = ∫ u : ℝ, H (v - s * u) * ψ u := by
  have hsne : s ≠ 0 := ne_of_gt hs
  have h := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => (1 / s) * ψ (t / s) * H (v - t)) s
  rw [abs_of_pos (inv_pos.mpr hs)] at h
  have hsub : (∫ x, (fun t : ℝ => (1 / s) * ψ (t / s) * H (v - t)) (s * x))
      = ∫ x, (1 / s) * ψ x * H (v - s * x) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [mul_div_cancel_left₀ x hsne]
  rw [hsub] at h
  have h' : (∫ y, (1 / s) * ψ (y / s) * H (v - y)) = s • ∫ x, (1 / s) * ψ x * H (v - s * x) := by
    have h2 := congrArg (fun z : ℝ => s • z) h.symm
    rw [smul_smul, mul_inv_cancel₀ hsne, one_smul] at h2
    exact h2
  rw [h', ← MeasureTheory.integral_smul]
  apply integral_congr_ae
  filter_upwards with x
  rw [smul_eq_mul]
  field_simp

/-- `∫ t, g (t / s) = s • ∫ u, g u` for `s > 0` (values in a real normed space). -/
lemma integral_comp_div_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ → F) {s : ℝ} (hs : 0 < s) :
    (∫ t : ℝ, g (t / s)) = s • ∫ u : ℝ, g u := by
  rw [show (∫ t : ℝ, g (t / s)) = ∫ x : ℝ, g (s⁻¹ * x) from by
    apply integral_congr_ae
    filter_upwards with t
    rw [div_eq_inv_mul]]
  rw [MeasureTheory.Measure.integral_comp_mul_left g s⁻¹, inv_inv, abs_of_pos hs]

/-- Scaling of the Fourier transform: `Fhat (fun t => s⁻¹ ψ (t/s)) x = Fhat ψ (s x)` for `s > 0`. -/
lemma Fhat_smul_div {ψ : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (x : ℝ) :
    Fhat (fun t : ℝ => (1 / s) * ψ (t / s)) x = Fhat ψ (s * x) := by
  have hsne : s ≠ 0 := ne_of_gt hs
  rw [Fhat_eq_integral', Fhat_eq_integral']
  have hL : (∫ t : ℝ, (((1 / s) * ψ (t / s) : ℝ) : ℂ) * efun (-(t * x)))
      = s⁻¹ • (∫ t : ℝ, ((ψ (t / s) : ℝ) : ℂ) * efun (-(t / s * (s * x)))) := by
    rw [← MeasureTheory.integral_smul]
    apply integral_congr_ae
    filter_upwards with t
    have harg : t / s * (s * x) = t * x := by field_simp
    rw [show -(t / s * (s * x)) = -(t * x) by rw [harg]]
    rw [Complex.real_smul]
    push_cast
    ring
  have hg : (∫ t : ℝ, ((ψ (t / s) : ℝ) : ℂ) * efun (-(t / s * (s * x))))
      = s • (∫ u : ℝ, ((ψ u : ℝ) : ℂ) * efun (-(u * (s * x)))) :=
    integral_comp_div_smul (fun u : ℝ => ((ψ u : ℝ) : ℂ) * efun (-(u * (s * x)))) hs
  rw [hL, hg, smul_smul, inv_mul_cancel₀ hsne, one_smul]

/-- `Afun f M₂ K T` is the convolution of `Hprof f M₂` with the rescaled kernel
`ρ t = s⁻¹ ψ (t/s)`, `s = smScale K T M₂`. -/
lemma Afun_eq_convolution {f : ℝ → ℝ} {M₂ K T : ℝ} (hM₂ : 0 < M₂) (hK : 0 < K) (hT : 0 < T) :
    Afun f M₂ K T
      = MeasureTheory.convolution
          (fun t : ℝ => (1 / smScale K T M₂) * psiSmooth (t / smScale K T M₂))
          (Hprof f M₂) (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume := by
  funext v
  rw [Afun, MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact (integral_smul_comp_mul (ψ := psiSmooth) (H := Hprof f M₂)
    (smScale_pos hK hT hM₂) v).symm

theorem nearcorr_Afun_fhat {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {f : ℝ → ℝ} (hf : Continuous f) (hsup : SuppHyp C₀ f)
    {M₂ K T : ℝ} (hM₂ : 0 < M₂) (hK : 0 < K) (hT : 0 < T) (x : ℝ) :
    Fhat (Afun f M₂ K T) x = Fhat (Hprof f M₂) x * Fhat psiSmooth (smScale K T M₂ * x) := by
  have hs : 0 < smScale K T M₂ := smScale_pos hK hT hM₂
  have hHcs : HasCompactSupport (Hprof f M₂) := Hprof_hasCompactSupport hsup hC₀ hM₂.le
  have hHint : Integrable (Hprof f M₂) :=
    (Hprof_continuous hf M₂).integrable_of_hasCompactSupport hHcs
  have hρcont : Continuous (fun t : ℝ => (1 / smScale K T M₂) * psiSmooth (t / smScale K T M₂)) :=
    continuous_const.mul (psiSmooth_contDiff.continuous.comp (continuous_id.div_const _))
  have hρcs : HasCompactSupport (fun t : ℝ => (1 / smScale K T M₂) * psiSmooth (t / smScale K T M₂)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (-(smScale K T M₂)) (smScale K T M₂)) isCompact_Icc ?_
    intro t ht
    rw [Function.mem_support] at ht
    have ht' : (1 / smScale K T M₂) * psiSmooth (t / smScale K T M₂) ≠ 0 := ht
    have hψ : psiSmooth (t / smScale K T M₂) ≠ 0 := (mul_ne_zero_iff.mp ht').2
    have h2 := psiSmooth_support hψ
    rw [Set.mem_Icc] at h2 ⊢
    constructor
    · have := (le_div_iff₀ hs).mp h2.1
      simpa using this
    · have := (div_le_iff₀ hs).mp h2.2
      simpa using this
  have hρint : Integrable (fun t : ℝ => (1 / smScale K T M₂) * psiSmooth (t / smScale K T M₂)) :=
    hρcont.integrable_of_hasCompactSupport hρcs
  rw [Afun_eq_convolution hM₂ hK hT,
    Fhat_convolution_eq (φ := fun t : ℝ => (1 / smScale K T M₂) * psiSmooth (t / smScale K T M₂))
      (f := Hprof f M₂) hρcont hρcs hHint x,
    Fhat_smul_div hs x]
  exact mul_comm _ _

end

end Work.GM.Affine
